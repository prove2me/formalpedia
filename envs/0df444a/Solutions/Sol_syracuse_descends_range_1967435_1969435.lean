-- Prove2me | solution 1 for syracuse_descends_range_1967435_1969435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:58.582191+00:00
-- url     : https://prove2.me/submissions/c4595dcd-7972-437a-8520-d1f3bf130a39

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

theorem B2213365 : Blo 1967435 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B2951153 : Blo 1967435 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B1967435 : Blo 1967435 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B2490041 : Blo 1967435 2490041 := bbase (se 2 (by rfl) ⟨933765, by rfl⟩ : syracuseStep 2490041 = 1867531) (by norm_num)
theorem B6640109 : Blo 1967435 6640109 := bstep (se 3 (by rfl) ⟨1245020, by rfl⟩ : syracuseStep 6640109 = 2490041) B2490041
theorem B4426739 : Blo 1967435 4426739 := bstep (se 1 (by rfl) ⟨3320054, by rfl⟩ : syracuseStep 4426739 = 6640109) B6640109
theorem B2951159 : Blo 1967435 2951159 := bstep (se 1 (by rfl) ⟨2213369, by rfl⟩ : syracuseStep 2951159 = 4426739) B4426739
theorem B1967439 : Blo 1967435 1967439 := bstep (se 1 (by rfl) ⟨1475579, by rfl⟩ : syracuseStep 1967439 = 2951159) B2951159
theorem B2951165 : Blo 1967435 2951165 := bbase (se 3 (by rfl) ⟨553343, by rfl⟩ : syracuseStep 2951165 = 1106687) (by norm_num)
theorem B1967443 : Blo 1967435 1967443 := bstep (se 1 (by rfl) ⟨1475582, by rfl⟩ : syracuseStep 1967443 = 2951165) B2951165
theorem B4426757 : Blo 1967435 4426757 := bbase (se 4 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 4426757 = 830017) (by norm_num)
theorem B2951171 : Blo 1967435 2951171 := bstep (se 1 (by rfl) ⟨2213378, by rfl⟩ : syracuseStep 2951171 = 4426757) B4426757
theorem B1967447 : Blo 1967435 1967447 := bstep (se 1 (by rfl) ⟨1475585, by rfl⟩ : syracuseStep 1967447 = 2951171) B2951171
theorem B3735085 : Blo 1967435 3735085 := bbase (se 3 (by rfl) ⟨700328, by rfl⟩ : syracuseStep 3735085 = 1400657) (by norm_num)
theorem B4980113 : Blo 1967435 4980113 := bstep (se 2 (by rfl) ⟨1867542, by rfl⟩ : syracuseStep 4980113 = 3735085) B3735085
theorem B3320075 : Blo 1967435 3320075 := bstep (se 1 (by rfl) ⟨2490056, by rfl⟩ : syracuseStep 3320075 = 4980113) B4980113
theorem B2213383 : Blo 1967435 2213383 := bstep (se 1 (by rfl) ⟨1660037, by rfl⟩ : syracuseStep 2213383 = 3320075) B3320075
theorem B2951177 : Blo 1967435 2951177 := bstep (se 2 (by rfl) ⟨1106691, by rfl⟩ : syracuseStep 2951177 = 2213383) B2213383
theorem B1967451 : Blo 1967435 1967451 := bstep (se 1 (by rfl) ⟨1475588, by rfl⟩ : syracuseStep 1967451 = 2951177) B2951177
theorem B9960245 : Blo 1967435 9960245 := bbase (se 5 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 9960245 = 933773) (by norm_num)
theorem B6640163 : Blo 1967435 6640163 := bstep (se 1 (by rfl) ⟨4980122, by rfl⟩ : syracuseStep 6640163 = 9960245) B9960245
theorem B4426775 : Blo 1967435 4426775 := bstep (se 1 (by rfl) ⟨3320081, by rfl⟩ : syracuseStep 4426775 = 6640163) B6640163
theorem B2951183 : Blo 1967435 2951183 := bstep (se 1 (by rfl) ⟨2213387, by rfl⟩ : syracuseStep 2951183 = 4426775) B4426775
theorem B1967455 : Blo 1967435 1967455 := bstep (se 1 (by rfl) ⟨1475591, by rfl⟩ : syracuseStep 1967455 = 2951183) B2951183
theorem B2951189 : Blo 1967435 2951189 := bbase (se 6 (by rfl) ⟨69168, by rfl⟩ : syracuseStep 2951189 = 138337) (by norm_num)
theorem B1967459 : Blo 1967435 1967459 := bstep (se 1 (by rfl) ⟨1475594, by rfl⟩ : syracuseStep 1967459 = 2951189) B2951189
theorem B6730789 : Blo 1967435 6730789 := bbase (se 4 (by rfl) ⟨631011, by rfl⟩ : syracuseStep 6730789 = 1262023) (by norm_num)
theorem B8974385 : Blo 1967435 8974385 := bstep (se 2 (by rfl) ⟨3365394, by rfl⟩ : syracuseStep 8974385 = 6730789) B6730789
theorem B5982923 : Blo 1967435 5982923 := bstep (se 1 (by rfl) ⟨4487192, by rfl⟩ : syracuseStep 5982923 = 8974385) B8974385
theorem B3988615 : Blo 1967435 3988615 := bstep (se 1 (by rfl) ⟨2991461, by rfl⟩ : syracuseStep 3988615 = 5982923) B5982923
theorem B5318153 : Blo 1967435 5318153 := bstep (se 2 (by rfl) ⟨1994307, by rfl⟩ : syracuseStep 5318153 = 3988615) B3988615
theorem B3545435 : Blo 1967435 3545435 := bstep (se 1 (by rfl) ⟨2659076, by rfl⟩ : syracuseStep 3545435 = 5318153) B5318153
theorem B2363623 : Blo 1967435 2363623 := bstep (se 1 (by rfl) ⟨1772717, by rfl⟩ : syracuseStep 2363623 = 3545435) B3545435
theorem B12605989 : Blo 1967435 12605989 := bstep (se 4 (by rfl) ⟨1181811, by rfl⟩ : syracuseStep 12605989 = 2363623) B2363623
theorem B16807985 : Blo 1967435 16807985 := bstep (se 2 (by rfl) ⟨6302994, by rfl⟩ : syracuseStep 16807985 = 12605989) B12605989
theorem B11205323 : Blo 1967435 11205323 := bstep (se 1 (by rfl) ⟨8403992, by rfl⟩ : syracuseStep 11205323 = 16807985) B16807985
theorem B7470215 : Blo 1967435 7470215 := bstep (se 1 (by rfl) ⟨5602661, by rfl⟩ : syracuseStep 7470215 = 11205323) B11205323
theorem B4980143 : Blo 1967435 4980143 := bstep (se 1 (by rfl) ⟨3735107, by rfl⟩ : syracuseStep 4980143 = 7470215) B7470215
theorem B3320095 : Blo 1967435 3320095 := bstep (se 1 (by rfl) ⟨2490071, by rfl⟩ : syracuseStep 3320095 = 4980143) B4980143
theorem B4426793 : Blo 1967435 4426793 := bstep (se 2 (by rfl) ⟨1660047, by rfl⟩ : syracuseStep 4426793 = 3320095) B3320095
theorem B2951195 : Blo 1967435 2951195 := bstep (se 1 (by rfl) ⟨2213396, by rfl⟩ : syracuseStep 2951195 = 4426793) B4426793
theorem B1967463 : Blo 1967435 1967463 := bstep (se 1 (by rfl) ⟨1475597, by rfl⟩ : syracuseStep 1967463 = 2951195) B2951195
theorem B2213401 : Blo 1967435 2213401 := bbase (se 2 (by rfl) ⟨830025, by rfl⟩ : syracuseStep 2213401 = 1660051) (by norm_num)
theorem B2951201 : Blo 1967435 2951201 := bstep (se 2 (by rfl) ⟨1106700, by rfl⟩ : syracuseStep 2951201 = 2213401) B2213401
theorem B1967467 : Blo 1967435 1967467 := bstep (se 1 (by rfl) ⟨1475600, by rfl⟩ : syracuseStep 1967467 = 2951201) B2951201
theorem B7470245 : Blo 1967435 7470245 := bbase (se 4 (by rfl) ⟨700335, by rfl⟩ : syracuseStep 7470245 = 1400671) (by norm_num)
theorem B4980163 : Blo 1967435 4980163 := bstep (se 1 (by rfl) ⟨3735122, by rfl⟩ : syracuseStep 4980163 = 7470245) B7470245
theorem B6640217 : Blo 1967435 6640217 := bstep (se 2 (by rfl) ⟨2490081, by rfl⟩ : syracuseStep 6640217 = 4980163) B4980163
theorem B4426811 : Blo 1967435 4426811 := bstep (se 1 (by rfl) ⟨3320108, by rfl⟩ : syracuseStep 4426811 = 6640217) B6640217
theorem B2951207 : Blo 1967435 2951207 := bstep (se 1 (by rfl) ⟨2213405, by rfl⟩ : syracuseStep 2951207 = 4426811) B4426811
theorem B1967471 : Blo 1967435 1967471 := bstep (se 1 (by rfl) ⟨1475603, by rfl⟩ : syracuseStep 1967471 = 2951207) B2951207
theorem B2951213 : Blo 1967435 2951213 := bbase (se 3 (by rfl) ⟨553352, by rfl⟩ : syracuseStep 2951213 = 1106705) (by norm_num)
theorem B1967475 : Blo 1967435 1967475 := bstep (se 1 (by rfl) ⟨1475606, by rfl⟩ : syracuseStep 1967475 = 2951213) B2951213
theorem B4426829 : Blo 1967435 4426829 := bbase (se 3 (by rfl) ⟨830030, by rfl⟩ : syracuseStep 4426829 = 1660061) (by norm_num)
theorem B2951219 : Blo 1967435 2951219 := bstep (se 1 (by rfl) ⟨2213414, by rfl⟩ : syracuseStep 2951219 = 4426829) B4426829
theorem B1967479 : Blo 1967435 1967479 := bstep (se 1 (by rfl) ⟨1475609, by rfl⟩ : syracuseStep 1967479 = 2951219) B2951219
theorem B2490097 : Blo 1967435 2490097 := bbase (se 2 (by rfl) ⟨933786, by rfl⟩ : syracuseStep 2490097 = 1867573) (by norm_num)
theorem B3320129 : Blo 1967435 3320129 := bstep (se 2 (by rfl) ⟨1245048, by rfl⟩ : syracuseStep 3320129 = 2490097) B2490097
theorem B2213419 : Blo 1967435 2213419 := bstep (se 1 (by rfl) ⟨1660064, by rfl⟩ : syracuseStep 2213419 = 3320129) B3320129
theorem B2951225 : Blo 1967435 2951225 := bstep (se 2 (by rfl) ⟨1106709, by rfl⟩ : syracuseStep 2951225 = 2213419) B2213419
theorem B1967483 : Blo 1967435 1967483 := bstep (se 1 (by rfl) ⟨1475612, by rfl⟩ : syracuseStep 1967483 = 2951225) B2951225
theorem B5679173 : Blo 1967435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 1967435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 1967435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 1967435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 1967435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2991497 : Blo 1967435 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B31909301 : Blo 1967435 31909301 := bstep (se 5 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 31909301 = 2991497) B2991497
theorem B21272867 : Blo 1967435 21272867 := bstep (se 1 (by rfl) ⟨15954650, by rfl⟩ : syracuseStep 21272867 = 31909301) B31909301
theorem B14181911 : Blo 1967435 14181911 := bstep (se 1 (by rfl) ⟨10636433, by rfl⟩ : syracuseStep 14181911 = 21272867) B21272867
theorem B9454607 : Blo 1967435 9454607 := bstep (se 1 (by rfl) ⟨7090955, by rfl⟩ : syracuseStep 9454607 = 14181911) B14181911
theorem B6303071 : Blo 1967435 6303071 := bstep (se 1 (by rfl) ⟨4727303, by rfl⟩ : syracuseStep 6303071 = 9454607) B9454607
theorem B4202047 : Blo 1967435 4202047 := bstep (se 1 (by rfl) ⟨3151535, by rfl⟩ : syracuseStep 4202047 = 6303071) B6303071
theorem B22410917 : Blo 1967435 22410917 := bstep (se 4 (by rfl) ⟨2101023, by rfl⟩ : syracuseStep 22410917 = 4202047) B4202047
theorem B14940611 : Blo 1967435 14940611 := bstep (se 1 (by rfl) ⟨11205458, by rfl⟩ : syracuseStep 14940611 = 22410917) B22410917
theorem B9960407 : Blo 1967435 9960407 := bstep (se 1 (by rfl) ⟨7470305, by rfl⟩ : syracuseStep 9960407 = 14940611) B14940611
theorem B6640271 : Blo 1967435 6640271 := bstep (se 1 (by rfl) ⟨4980203, by rfl⟩ : syracuseStep 6640271 = 9960407) B9960407
theorem B4426847 : Blo 1967435 4426847 := bstep (se 1 (by rfl) ⟨3320135, by rfl⟩ : syracuseStep 4426847 = 6640271) B6640271
theorem B2951231 : Blo 1967435 2951231 := bstep (se 1 (by rfl) ⟨2213423, by rfl⟩ : syracuseStep 2951231 = 4426847) B4426847
theorem B1967487 : Blo 1967435 1967487 := bstep (se 1 (by rfl) ⟨1475615, by rfl⟩ : syracuseStep 1967487 = 2951231) B2951231
theorem B2951237 : Blo 1967435 2951237 := bbase (se 4 (by rfl) ⟨276678, by rfl⟩ : syracuseStep 2951237 = 553357) (by norm_num)
theorem B1967491 : Blo 1967435 1967491 := bstep (se 1 (by rfl) ⟨1475618, by rfl⟩ : syracuseStep 1967491 = 2951237) B2951237
theorem B3320149 : Blo 1967435 3320149 := bbase (se 10 (by rfl) ⟨4863, by rfl⟩ : syracuseStep 3320149 = 9727) (by norm_num)
theorem B4426865 : Blo 1967435 4426865 := bstep (se 2 (by rfl) ⟨1660074, by rfl⟩ : syracuseStep 4426865 = 3320149) B3320149
theorem B2951243 : Blo 1967435 2951243 := bstep (se 1 (by rfl) ⟨2213432, by rfl⟩ : syracuseStep 2951243 = 4426865) B4426865
theorem B1967495 : Blo 1967435 1967495 := bstep (se 1 (by rfl) ⟨1475621, by rfl⟩ : syracuseStep 1967495 = 2951243) B2951243
theorem B2213437 : Blo 1967435 2213437 := bbase (se 3 (by rfl) ⟨415019, by rfl⟩ : syracuseStep 2213437 = 830039) (by norm_num)
theorem B2951249 : Blo 1967435 2951249 := bstep (se 2 (by rfl) ⟨1106718, by rfl⟩ : syracuseStep 2951249 = 2213437) B2213437
theorem B1967499 : Blo 1967435 1967499 := bstep (se 1 (by rfl) ⟨1475624, by rfl⟩ : syracuseStep 1967499 = 2951249) B2951249
theorem B6640325 : Blo 1967435 6640325 := bbase (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) (by norm_num)
theorem B4426883 : Blo 1967435 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B2951255 : Blo 1967435 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B1967503 : Blo 1967435 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B2951261 : Blo 1967435 2951261 := bbase (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) (by norm_num)
theorem B1967507 : Blo 1967435 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B4426901 : Blo 1967435 4426901 := bbase (se 6 (by rfl) ⟨103755, by rfl⟩ : syracuseStep 4426901 = 207511) (by norm_num)
theorem B2951267 : Blo 1967435 2951267 := bstep (se 1 (by rfl) ⟨2213450, by rfl⟩ : syracuseStep 2951267 = 4426901) B4426901
theorem B1967511 : Blo 1967435 1967511 := bstep (se 1 (by rfl) ⟨1475633, by rfl⟩ : syracuseStep 1967511 = 2951267) B2951267
theorem B2801405 : Blo 1967435 2801405 := bbase (se 3 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 2801405 = 1050527) (by norm_num)
theorem B7470413 : Blo 1967435 7470413 := bstep (se 3 (by rfl) ⟨1400702, by rfl⟩ : syracuseStep 7470413 = 2801405) B2801405
theorem B4980275 : Blo 1967435 4980275 := bstep (se 1 (by rfl) ⟨3735206, by rfl⟩ : syracuseStep 4980275 = 7470413) B7470413
theorem B3320183 : Blo 1967435 3320183 := bstep (se 1 (by rfl) ⟨2490137, by rfl⟩ : syracuseStep 3320183 = 4980275) B4980275
theorem B2213455 : Blo 1967435 2213455 := bstep (se 1 (by rfl) ⟨1660091, by rfl⟩ : syracuseStep 2213455 = 3320183) B3320183
theorem B2951273 : Blo 1967435 2951273 := bstep (se 2 (by rfl) ⟨1106727, by rfl⟩ : syracuseStep 2951273 = 2213455) B2213455
theorem B1967515 : Blo 1967435 1967515 := bstep (se 1 (by rfl) ⟨1475636, by rfl⟩ : syracuseStep 1967515 = 2951273) B2951273
theorem B18194165 : Blo 1967435 18194165 := bbase (se 5 (by rfl) ⟨852851, by rfl⟩ : syracuseStep 18194165 = 1705703) (by norm_num)
theorem B12129443 : Blo 1967435 12129443 := bstep (se 1 (by rfl) ⟨9097082, by rfl⟩ : syracuseStep 12129443 = 18194165) B18194165
theorem B8086295 : Blo 1967435 8086295 := bstep (se 1 (by rfl) ⟨6064721, by rfl⟩ : syracuseStep 8086295 = 12129443) B12129443
theorem B21563453 : Blo 1967435 21563453 := bstep (se 3 (by rfl) ⟨4043147, by rfl⟩ : syracuseStep 21563453 = 8086295) B8086295
theorem B57502541 : Blo 1967435 57502541 := bstep (se 3 (by rfl) ⟨10781726, by rfl⟩ : syracuseStep 57502541 = 21563453) B21563453
theorem B38335027 : Blo 1967435 38335027 := bstep (se 1 (by rfl) ⟨28751270, by rfl⟩ : syracuseStep 38335027 = 57502541) B57502541
theorem B51113369 : Blo 1967435 51113369 := bstep (se 2 (by rfl) ⟨19167513, by rfl⟩ : syracuseStep 51113369 = 38335027) B38335027
theorem B34075579 : Blo 1967435 34075579 := bstep (se 1 (by rfl) ⟨25556684, by rfl⟩ : syracuseStep 34075579 = 51113369) B51113369
theorem B45434105 : Blo 1967435 45434105 := bstep (se 2 (by rfl) ⟨17037789, by rfl⟩ : syracuseStep 45434105 = 34075579) B34075579
theorem B30289403 : Blo 1967435 30289403 := bstep (se 1 (by rfl) ⟨22717052, by rfl⟩ : syracuseStep 30289403 = 45434105) B45434105
theorem B20192935 : Blo 1967435 20192935 := bstep (se 1 (by rfl) ⟨15144701, by rfl⟩ : syracuseStep 20192935 = 30289403) B30289403
theorem B26923913 : Blo 1967435 26923913 := bstep (se 2 (by rfl) ⟨10096467, by rfl⟩ : syracuseStep 26923913 = 20192935) B20192935
theorem B17949275 : Blo 1967435 17949275 := bstep (se 1 (by rfl) ⟨13461956, by rfl⟩ : syracuseStep 17949275 = 26923913) B26923913
theorem B11966183 : Blo 1967435 11966183 := bstep (se 1 (by rfl) ⟨8974637, by rfl⟩ : syracuseStep 11966183 = 17949275) B17949275
theorem B7977455 : Blo 1967435 7977455 := bstep (se 1 (by rfl) ⟨5983091, by rfl⟩ : syracuseStep 7977455 = 11966183) B11966183
theorem B5318303 : Blo 1967435 5318303 := bstep (se 1 (by rfl) ⟨3988727, by rfl⟩ : syracuseStep 5318303 = 7977455) B7977455
theorem B14182141 : Blo 1967435 14182141 := bstep (se 3 (by rfl) ⟨2659151, by rfl⟩ : syracuseStep 14182141 = 5318303) B5318303
theorem B18909521 : Blo 1967435 18909521 := bstep (se 2 (by rfl) ⟨7091070, by rfl⟩ : syracuseStep 18909521 = 14182141) B14182141
theorem B12606347 : Blo 1967435 12606347 := bstep (se 1 (by rfl) ⟨9454760, by rfl⟩ : syracuseStep 12606347 = 18909521) B18909521
theorem B8404231 : Blo 1967435 8404231 := bstep (se 1 (by rfl) ⟨6303173, by rfl⟩ : syracuseStep 8404231 = 12606347) B12606347
theorem B11205641 : Blo 1967435 11205641 := bstep (se 2 (by rfl) ⟨4202115, by rfl⟩ : syracuseStep 11205641 = 8404231) B8404231
theorem B7470427 : Blo 1967435 7470427 := bstep (se 1 (by rfl) ⟨5602820, by rfl⟩ : syracuseStep 7470427 = 11205641) B11205641
theorem B9960569 : Blo 1967435 9960569 := bstep (se 2 (by rfl) ⟨3735213, by rfl⟩ : syracuseStep 9960569 = 7470427) B7470427
theorem B6640379 : Blo 1967435 6640379 := bstep (se 1 (by rfl) ⟨4980284, by rfl⟩ : syracuseStep 6640379 = 9960569) B9960569
theorem B4426919 : Blo 1967435 4426919 := bstep (se 1 (by rfl) ⟨3320189, by rfl⟩ : syracuseStep 4426919 = 6640379) B6640379
theorem B2951279 : Blo 1967435 2951279 := bstep (se 1 (by rfl) ⟨2213459, by rfl⟩ : syracuseStep 2951279 = 4426919) B4426919
theorem B1967519 : Blo 1967435 1967519 := bstep (se 1 (by rfl) ⟨1475639, by rfl⟩ : syracuseStep 1967519 = 2951279) B2951279
theorem B2951285 : Blo 1967435 2951285 := bbase (se 5 (by rfl) ⟨138341, by rfl⟩ : syracuseStep 2951285 = 276683) (by norm_num)
theorem B1967523 : Blo 1967435 1967523 := bstep (se 1 (by rfl) ⟨1475642, by rfl⟩ : syracuseStep 1967523 = 2951285) B2951285
theorem B3735229 : Blo 1967435 3735229 := bbase (se 3 (by rfl) ⟨700355, by rfl⟩ : syracuseStep 3735229 = 1400711) (by norm_num)
theorem B4980305 : Blo 1967435 4980305 := bstep (se 2 (by rfl) ⟨1867614, by rfl⟩ : syracuseStep 4980305 = 3735229) B3735229
theorem B3320203 : Blo 1967435 3320203 := bstep (se 1 (by rfl) ⟨2490152, by rfl⟩ : syracuseStep 3320203 = 4980305) B4980305
theorem B4426937 : Blo 1967435 4426937 := bstep (se 2 (by rfl) ⟨1660101, by rfl⟩ : syracuseStep 4426937 = 3320203) B3320203
theorem B2951291 : Blo 1967435 2951291 := bstep (se 1 (by rfl) ⟨2213468, by rfl⟩ : syracuseStep 2951291 = 4426937) B4426937
theorem B1967527 : Blo 1967435 1967527 := bstep (se 1 (by rfl) ⟨1475645, by rfl⟩ : syracuseStep 1967527 = 2951291) B2951291
theorem B2213473 : Blo 1967435 2213473 := bbase (se 2 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 2213473 = 1660105) (by norm_num)
theorem B2951297 : Blo 1967435 2951297 := bstep (se 2 (by rfl) ⟨1106736, by rfl⟩ : syracuseStep 2951297 = 2213473) B2213473
theorem B1967531 : Blo 1967435 1967531 := bstep (se 1 (by rfl) ⟨1475648, by rfl⟩ : syracuseStep 1967531 = 2951297) B2951297
theorem B4980325 : Blo 1967435 4980325 := bbase (se 4 (by rfl) ⟨466905, by rfl⟩ : syracuseStep 4980325 = 933811) (by norm_num)
theorem B6640433 : Blo 1967435 6640433 := bstep (se 2 (by rfl) ⟨2490162, by rfl⟩ : syracuseStep 6640433 = 4980325) B4980325
theorem B4426955 : Blo 1967435 4426955 := bstep (se 1 (by rfl) ⟨3320216, by rfl⟩ : syracuseStep 4426955 = 6640433) B6640433
theorem B2951303 : Blo 1967435 2951303 := bstep (se 1 (by rfl) ⟨2213477, by rfl⟩ : syracuseStep 2951303 = 4426955) B4426955
theorem B1967535 : Blo 1967435 1967535 := bstep (se 1 (by rfl) ⟨1475651, by rfl⟩ : syracuseStep 1967535 = 2951303) B2951303
theorem B2951309 : Blo 1967435 2951309 := bbase (se 3 (by rfl) ⟨553370, by rfl⟩ : syracuseStep 2951309 = 1106741) (by norm_num)
theorem B1967539 : Blo 1967435 1967539 := bstep (se 1 (by rfl) ⟨1475654, by rfl⟩ : syracuseStep 1967539 = 2951309) B2951309
theorem B4426973 : Blo 1967435 4426973 := bbase (se 3 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 4426973 = 1660115) (by norm_num)
theorem B2951315 : Blo 1967435 2951315 := bstep (se 1 (by rfl) ⟨2213486, by rfl⟩ : syracuseStep 2951315 = 4426973) B4426973
theorem B1967543 : Blo 1967435 1967543 := bstep (se 1 (by rfl) ⟨1475657, by rfl⟩ : syracuseStep 1967543 = 2951315) B2951315
theorem B3320237 : Blo 1967435 3320237 := bbase (se 3 (by rfl) ⟨622544, by rfl⟩ : syracuseStep 3320237 = 1245089) (by norm_num)
theorem B2213491 : Blo 1967435 2213491 := bstep (se 1 (by rfl) ⟨1660118, by rfl⟩ : syracuseStep 2213491 = 3320237) B3320237
theorem B2951321 : Blo 1967435 2951321 := bstep (se 2 (by rfl) ⟨1106745, by rfl⟩ : syracuseStep 2951321 = 2213491) B2213491
theorem B1967547 : Blo 1967435 1967547 := bstep (se 1 (by rfl) ⟨1475660, by rfl⟩ : syracuseStep 1967547 = 2951321) B2951321
theorem B6564805 : Blo 1967435 6564805 := bbase (se 4 (by rfl) ⟨615450, by rfl⟩ : syracuseStep 6564805 = 1230901) (by norm_num)
theorem B35012293 : Blo 1967435 35012293 := bstep (se 4 (by rfl) ⟨3282402, by rfl⟩ : syracuseStep 35012293 = 6564805) B6564805
theorem B186732229 : Blo 1967435 186732229 := bstep (se 4 (by rfl) ⟨17506146, by rfl⟩ : syracuseStep 186732229 = 35012293) B35012293
theorem B248976305 : Blo 1967435 248976305 := bstep (se 2 (by rfl) ⟨93366114, by rfl⟩ : syracuseStep 248976305 = 186732229) B186732229
theorem B165984203 : Blo 1967435 165984203 := bstep (se 1 (by rfl) ⟨124488152, by rfl⟩ : syracuseStep 165984203 = 248976305) B248976305
theorem B110656135 : Blo 1967435 110656135 := bstep (se 1 (by rfl) ⟨82992101, by rfl⟩ : syracuseStep 110656135 = 165984203) B165984203
theorem B147541513 : Blo 1967435 147541513 := bstep (se 2 (by rfl) ⟨55328067, by rfl⟩ : syracuseStep 147541513 = 110656135) B110656135
theorem B196722017 : Blo 1967435 196722017 := bstep (se 2 (by rfl) ⟨73770756, by rfl⟩ : syracuseStep 196722017 = 147541513) B147541513
theorem B131148011 : Blo 1967435 131148011 := bstep (se 1 (by rfl) ⟨98361008, by rfl⟩ : syracuseStep 131148011 = 196722017) B196722017
theorem B87432007 : Blo 1967435 87432007 := bstep (se 1 (by rfl) ⟨65574005, by rfl⟩ : syracuseStep 87432007 = 131148011) B131148011
theorem B116576009 : Blo 1967435 116576009 := bstep (se 2 (by rfl) ⟨43716003, by rfl⟩ : syracuseStep 116576009 = 87432007) B87432007
theorem B77717339 : Blo 1967435 77717339 := bstep (se 1 (by rfl) ⟨58288004, by rfl⟩ : syracuseStep 77717339 = 116576009) B116576009
theorem B51811559 : Blo 1967435 51811559 := bstep (se 1 (by rfl) ⟨38858669, by rfl⟩ : syracuseStep 51811559 = 77717339) B77717339
theorem B34541039 : Blo 1967435 34541039 := bstep (se 1 (by rfl) ⟨25905779, by rfl⟩ : syracuseStep 34541039 = 51811559) B51811559
theorem B23027359 : Blo 1967435 23027359 := bstep (se 1 (by rfl) ⟨17270519, by rfl⟩ : syracuseStep 23027359 = 34541039) B34541039
theorem B30703145 : Blo 1967435 30703145 := bstep (se 2 (by rfl) ⟨11513679, by rfl⟩ : syracuseStep 30703145 = 23027359) B23027359
theorem B81875053 : Blo 1967435 81875053 := bstep (se 3 (by rfl) ⟨15351572, by rfl⟩ : syracuseStep 81875053 = 30703145) B30703145
theorem B109166737 : Blo 1967435 109166737 := bstep (se 2 (by rfl) ⟨40937526, by rfl⟩ : syracuseStep 109166737 = 81875053) B81875053
theorem B145555649 : Blo 1967435 145555649 := bstep (se 2 (by rfl) ⟨54583368, by rfl⟩ : syracuseStep 145555649 = 109166737) B109166737
theorem B97037099 : Blo 1967435 97037099 := bstep (se 1 (by rfl) ⟨72777824, by rfl⟩ : syracuseStep 97037099 = 145555649) B145555649
theorem B64691399 : Blo 1967435 64691399 := bstep (se 1 (by rfl) ⟨48518549, by rfl⟩ : syracuseStep 64691399 = 97037099) B97037099
theorem B43127599 : Blo 1967435 43127599 := bstep (se 1 (by rfl) ⟨32345699, by rfl⟩ : syracuseStep 43127599 = 64691399) B64691399
theorem B57503465 : Blo 1967435 57503465 := bstep (se 2 (by rfl) ⟨21563799, by rfl⟩ : syracuseStep 57503465 = 43127599) B43127599
theorem B38335643 : Blo 1967435 38335643 := bstep (se 1 (by rfl) ⟨28751732, by rfl⟩ : syracuseStep 38335643 = 57503465) B57503465
theorem B25557095 : Blo 1967435 25557095 := bstep (se 1 (by rfl) ⟨19167821, by rfl⟩ : syracuseStep 25557095 = 38335643) B38335643
theorem B17038063 : Blo 1967435 17038063 := bstep (se 1 (by rfl) ⟨12778547, by rfl⟩ : syracuseStep 17038063 = 25557095) B25557095
theorem B22717417 : Blo 1967435 22717417 := bstep (se 2 (by rfl) ⟨8519031, by rfl⟩ : syracuseStep 22717417 = 17038063) B17038063
theorem B30289889 : Blo 1967435 30289889 := bstep (se 2 (by rfl) ⟨11358708, by rfl⟩ : syracuseStep 30289889 = 22717417) B22717417
theorem B80773037 : Blo 1967435 80773037 := bstep (se 3 (by rfl) ⟨15144944, by rfl⟩ : syracuseStep 80773037 = 30289889) B30289889
theorem B53848691 : Blo 1967435 53848691 := bstep (se 1 (by rfl) ⟨40386518, by rfl⟩ : syracuseStep 53848691 = 80773037) B80773037
theorem B35899127 : Blo 1967435 35899127 := bstep (se 1 (by rfl) ⟨26924345, by rfl⟩ : syracuseStep 35899127 = 53848691) B53848691
theorem B23932751 : Blo 1967435 23932751 := bstep (se 1 (by rfl) ⟨17949563, by rfl⟩ : syracuseStep 23932751 = 35899127) B35899127
theorem B63820669 : Blo 1967435 63820669 := bstep (se 3 (by rfl) ⟨11966375, by rfl⟩ : syracuseStep 63820669 = 23932751) B23932751
theorem B85094225 : Blo 1967435 85094225 := bstep (se 2 (by rfl) ⟨31910334, by rfl⟩ : syracuseStep 85094225 = 63820669) B63820669
theorem B56729483 : Blo 1967435 56729483 := bstep (se 1 (by rfl) ⟨42547112, by rfl⟩ : syracuseStep 56729483 = 85094225) B85094225
theorem B37819655 : Blo 1967435 37819655 := bstep (se 1 (by rfl) ⟨28364741, by rfl⟩ : syracuseStep 37819655 = 56729483) B56729483
theorem B25213103 : Blo 1967435 25213103 := bstep (se 1 (by rfl) ⟨18909827, by rfl⟩ : syracuseStep 25213103 = 37819655) B37819655
theorem B16808735 : Blo 1967435 16808735 := bstep (se 1 (by rfl) ⟨12606551, by rfl⟩ : syracuseStep 16808735 = 25213103) B25213103
theorem B11205823 : Blo 1967435 11205823 := bstep (se 1 (by rfl) ⟨8404367, by rfl⟩ : syracuseStep 11205823 = 16808735) B16808735
theorem B14941097 : Blo 1967435 14941097 := bstep (se 2 (by rfl) ⟨5602911, by rfl⟩ : syracuseStep 14941097 = 11205823) B11205823
theorem B9960731 : Blo 1967435 9960731 := bstep (se 1 (by rfl) ⟨7470548, by rfl⟩ : syracuseStep 9960731 = 14941097) B14941097
theorem B6640487 : Blo 1967435 6640487 := bstep (se 1 (by rfl) ⟨4980365, by rfl⟩ : syracuseStep 6640487 = 9960731) B9960731
theorem B4426991 : Blo 1967435 4426991 := bstep (se 1 (by rfl) ⟨3320243, by rfl⟩ : syracuseStep 4426991 = 6640487) B6640487
theorem B2951327 : Blo 1967435 2951327 := bstep (se 1 (by rfl) ⟨2213495, by rfl⟩ : syracuseStep 2951327 = 4426991) B4426991
theorem B1967551 : Blo 1967435 1967551 := bstep (se 1 (by rfl) ⟨1475663, by rfl⟩ : syracuseStep 1967551 = 2951327) B2951327
theorem B2951333 : Blo 1967435 2951333 := bbase (se 4 (by rfl) ⟨276687, by rfl⟩ : syracuseStep 2951333 = 553375) (by norm_num)
theorem B1967555 : Blo 1967435 1967555 := bstep (se 1 (by rfl) ⟨1475666, by rfl⟩ : syracuseStep 1967555 = 2951333) B2951333
theorem B2490193 : Blo 1967435 2490193 := bbase (se 2 (by rfl) ⟨933822, by rfl⟩ : syracuseStep 2490193 = 1867645) (by norm_num)
theorem B3320257 : Blo 1967435 3320257 := bstep (se 2 (by rfl) ⟨1245096, by rfl⟩ : syracuseStep 3320257 = 2490193) B2490193
theorem B4427009 : Blo 1967435 4427009 := bstep (se 2 (by rfl) ⟨1660128, by rfl⟩ : syracuseStep 4427009 = 3320257) B3320257
theorem B2951339 : Blo 1967435 2951339 := bstep (se 1 (by rfl) ⟨2213504, by rfl⟩ : syracuseStep 2951339 = 4427009) B4427009
theorem B1967559 : Blo 1967435 1967559 := bstep (se 1 (by rfl) ⟨1475669, by rfl⟩ : syracuseStep 1967559 = 2951339) B2951339
theorem B2213509 : Blo 1967435 2213509 := bbase (se 4 (by rfl) ⟨207516, by rfl⟩ : syracuseStep 2213509 = 415033) (by norm_num)
theorem B2951345 : Blo 1967435 2951345 := bstep (se 2 (by rfl) ⟨1106754, by rfl⟩ : syracuseStep 2951345 = 2213509) B2213509
theorem B1967563 : Blo 1967435 1967563 := bstep (se 1 (by rfl) ⟨1475672, by rfl⟩ : syracuseStep 1967563 = 2951345) B2951345
theorem B7977653 : Blo 1967435 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B5318435 : Blo 1967435 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B3545623 : Blo 1967435 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B4727497 : Blo 1967435 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B6303329 : Blo 1967435 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B4202219 : Blo 1967435 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B2801479 : Blo 1967435 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B3735305 : Blo 1967435 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B2490203 : Blo 1967435 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B6640541 : Blo 1967435 6640541 := bstep (se 3 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 6640541 = 2490203) B2490203
theorem B4427027 : Blo 1967435 4427027 := bstep (se 1 (by rfl) ⟨3320270, by rfl⟩ : syracuseStep 4427027 = 6640541) B6640541
theorem B2951351 : Blo 1967435 2951351 := bstep (se 1 (by rfl) ⟨2213513, by rfl⟩ : syracuseStep 2951351 = 4427027) B4427027
theorem B1967567 : Blo 1967435 1967567 := bstep (se 1 (by rfl) ⟨1475675, by rfl⟩ : syracuseStep 1967567 = 2951351) B2951351
theorem B2951357 : Blo 1967435 2951357 := bbase (se 3 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 2951357 = 1106759) (by norm_num)
theorem B1967571 : Blo 1967435 1967571 := bstep (se 1 (by rfl) ⟨1475678, by rfl⟩ : syracuseStep 1967571 = 2951357) B2951357
theorem B4427045 : Blo 1967435 4427045 := bbase (se 4 (by rfl) ⟨415035, by rfl⟩ : syracuseStep 4427045 = 830071) (by norm_num)
theorem B2951363 : Blo 1967435 2951363 := bstep (se 1 (by rfl) ⟨2213522, by rfl⟩ : syracuseStep 2951363 = 4427045) B4427045
theorem B1967575 : Blo 1967435 1967575 := bstep (se 1 (by rfl) ⟨1475681, by rfl⟩ : syracuseStep 1967575 = 2951363) B2951363
theorem B4980437 : Blo 1967435 4980437 := bbase (se 7 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 4980437 = 116729) (by norm_num)
theorem B3320291 : Blo 1967435 3320291 := bstep (se 1 (by rfl) ⟨2490218, by rfl⟩ : syracuseStep 3320291 = 4980437) B4980437
theorem B2213527 : Blo 1967435 2213527 := bstep (se 1 (by rfl) ⟨1660145, by rfl⟩ : syracuseStep 2213527 = 3320291) B3320291
theorem B2951369 : Blo 1967435 2951369 := bstep (se 2 (by rfl) ⟨1106763, by rfl⟩ : syracuseStep 2951369 = 2213527) B2213527
theorem B1967579 : Blo 1967435 1967579 := bstep (se 1 (by rfl) ⟨1475684, by rfl⟩ : syracuseStep 1967579 = 2951369) B2951369
theorem B1994429 : Blo 1967435 1994429 := bbase (se 3 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 1994429 = 747911) (by norm_num)
theorem B5318477 : Blo 1967435 5318477 := bstep (se 3 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 5318477 = 1994429) B1994429
theorem B3545651 : Blo 1967435 3545651 := bstep (se 1 (by rfl) ⟨2659238, by rfl⟩ : syracuseStep 3545651 = 5318477) B5318477
theorem B9455069 : Blo 1967435 9455069 := bstep (se 3 (by rfl) ⟨1772825, by rfl⟩ : syracuseStep 9455069 = 3545651) B3545651
theorem B6303379 : Blo 1967435 6303379 := bstep (se 1 (by rfl) ⟨4727534, by rfl⟩ : syracuseStep 6303379 = 9455069) B9455069
theorem B8404505 : Blo 1967435 8404505 := bstep (se 2 (by rfl) ⟨3151689, by rfl⟩ : syracuseStep 8404505 = 6303379) B6303379
theorem B5603003 : Blo 1967435 5603003 := bstep (se 1 (by rfl) ⟨4202252, by rfl⟩ : syracuseStep 5603003 = 8404505) B8404505
theorem B3735335 : Blo 1967435 3735335 := bstep (se 1 (by rfl) ⟨2801501, by rfl⟩ : syracuseStep 3735335 = 5603003) B5603003
theorem B9960893 : Blo 1967435 9960893 := bstep (se 3 (by rfl) ⟨1867667, by rfl⟩ : syracuseStep 9960893 = 3735335) B3735335
theorem B6640595 : Blo 1967435 6640595 := bstep (se 1 (by rfl) ⟨4980446, by rfl⟩ : syracuseStep 6640595 = 9960893) B9960893
theorem B4427063 : Blo 1967435 4427063 := bstep (se 1 (by rfl) ⟨3320297, by rfl⟩ : syracuseStep 4427063 = 6640595) B6640595
theorem B2951375 : Blo 1967435 2951375 := bstep (se 1 (by rfl) ⟨2213531, by rfl⟩ : syracuseStep 2951375 = 4427063) B4427063
theorem B1967583 : Blo 1967435 1967583 := bstep (se 1 (by rfl) ⟨1475687, by rfl⟩ : syracuseStep 1967583 = 2951375) B2951375
theorem B2951381 : Blo 1967435 2951381 := bbase (se 7 (by rfl) ⟨34586, by rfl⟩ : syracuseStep 2951381 = 69173) (by norm_num)
theorem B1967587 : Blo 1967435 1967587 := bstep (se 1 (by rfl) ⟨1475690, by rfl⟩ : syracuseStep 1967587 = 2951381) B2951381
theorem B7091333 : Blo 1967435 7091333 := bbase (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) (by norm_num)
theorem B4727555 : Blo 1967435 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B3151703 : Blo 1967435 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B2101135 : Blo 1967435 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B2801513 : Blo 1967435 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B7470701 : Blo 1967435 7470701 := bstep (se 3 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 7470701 = 2801513) B2801513
theorem B4980467 : Blo 1967435 4980467 := bstep (se 1 (by rfl) ⟨3735350, by rfl⟩ : syracuseStep 4980467 = 7470701) B7470701
theorem B3320311 : Blo 1967435 3320311 := bstep (se 1 (by rfl) ⟨2490233, by rfl⟩ : syracuseStep 3320311 = 4980467) B4980467
theorem B4427081 : Blo 1967435 4427081 := bstep (se 2 (by rfl) ⟨1660155, by rfl⟩ : syracuseStep 4427081 = 3320311) B3320311
theorem B2951387 : Blo 1967435 2951387 := bstep (se 1 (by rfl) ⟨2213540, by rfl⟩ : syracuseStep 2951387 = 4427081) B4427081
theorem B1967591 : Blo 1967435 1967591 := bstep (se 1 (by rfl) ⟨1475693, by rfl⟩ : syracuseStep 1967591 = 2951387) B2951387
theorem B2213545 : Blo 1967435 2213545 := bbase (se 2 (by rfl) ⟨830079, by rfl⟩ : syracuseStep 2213545 = 1660159) (by norm_num)
theorem B2951393 : Blo 1967435 2951393 := bstep (se 2 (by rfl) ⟨1106772, by rfl⟩ : syracuseStep 2951393 = 2213545) B2213545
theorem B1967595 : Blo 1967435 1967595 := bstep (se 1 (by rfl) ⟨1475696, by rfl⟩ : syracuseStep 1967595 = 2951393) B2951393
theorem B4727573 : Blo 1967435 4727573 := bbase (se 6 (by rfl) ⟨110802, by rfl⟩ : syracuseStep 4727573 = 221605) (by norm_num)
theorem B3151715 : Blo 1967435 3151715 := bstep (se 1 (by rfl) ⟨2363786, by rfl⟩ : syracuseStep 3151715 = 4727573) B4727573
theorem B8404573 : Blo 1967435 8404573 := bstep (se 3 (by rfl) ⟨1575857, by rfl⟩ : syracuseStep 8404573 = 3151715) B3151715
theorem B11206097 : Blo 1967435 11206097 := bstep (se 2 (by rfl) ⟨4202286, by rfl⟩ : syracuseStep 11206097 = 8404573) B8404573
theorem B7470731 : Blo 1967435 7470731 := bstep (se 1 (by rfl) ⟨5603048, by rfl⟩ : syracuseStep 7470731 = 11206097) B11206097
theorem B4980487 : Blo 1967435 4980487 := bstep (se 1 (by rfl) ⟨3735365, by rfl⟩ : syracuseStep 4980487 = 7470731) B7470731
theorem B6640649 : Blo 1967435 6640649 := bstep (se 2 (by rfl) ⟨2490243, by rfl⟩ : syracuseStep 6640649 = 4980487) B4980487
theorem B4427099 : Blo 1967435 4427099 := bstep (se 1 (by rfl) ⟨3320324, by rfl⟩ : syracuseStep 4427099 = 6640649) B6640649
theorem B2951399 : Blo 1967435 2951399 := bstep (se 1 (by rfl) ⟨2213549, by rfl⟩ : syracuseStep 2951399 = 4427099) B4427099
theorem B1967599 : Blo 1967435 1967599 := bstep (se 1 (by rfl) ⟨1475699, by rfl⟩ : syracuseStep 1967599 = 2951399) B2951399
theorem B2951405 : Blo 1967435 2951405 := bbase (se 3 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 2951405 = 1106777) (by norm_num)
theorem B1967603 : Blo 1967435 1967603 := bstep (se 1 (by rfl) ⟨1475702, by rfl⟩ : syracuseStep 1967603 = 2951405) B2951405
theorem B4427117 : Blo 1967435 4427117 := bbase (se 3 (by rfl) ⟨830084, by rfl⟩ : syracuseStep 4427117 = 1660169) (by norm_num)
theorem B2951411 : Blo 1967435 2951411 := bstep (se 1 (by rfl) ⟨2213558, by rfl⟩ : syracuseStep 2951411 = 4427117) B4427117
theorem B1967607 : Blo 1967435 1967607 := bstep (se 1 (by rfl) ⟨1475705, by rfl⟩ : syracuseStep 1967607 = 2951411) B2951411
theorem B3735389 : Blo 1967435 3735389 := bbase (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) (by norm_num)
theorem B2490259 : Blo 1967435 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B3320345 : Blo 1967435 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B2213563 : Blo 1967435 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B2951417 : Blo 1967435 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B1967611 : Blo 1967435 1967611 := bstep (se 1 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 1967611 = 2951417) B2951417
theorem B9455221 : Blo 1967435 9455221 := bbase (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) (by norm_num)
theorem B50427845 : Blo 1967435 50427845 := bstep (se 4 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 50427845 = 9455221) B9455221
theorem B33618563 : Blo 1967435 33618563 := bstep (se 1 (by rfl) ⟨25213922, by rfl⟩ : syracuseStep 33618563 = 50427845) B50427845
theorem B22412375 : Blo 1967435 22412375 := bstep (se 1 (by rfl) ⟨16809281, by rfl⟩ : syracuseStep 22412375 = 33618563) B33618563
theorem B14941583 : Blo 1967435 14941583 := bstep (se 1 (by rfl) ⟨11206187, by rfl⟩ : syracuseStep 14941583 = 22412375) B22412375
theorem B9961055 : Blo 1967435 9961055 := bstep (se 1 (by rfl) ⟨7470791, by rfl⟩ : syracuseStep 9961055 = 14941583) B14941583
theorem B6640703 : Blo 1967435 6640703 := bstep (se 1 (by rfl) ⟨4980527, by rfl⟩ : syracuseStep 6640703 = 9961055) B9961055
theorem B4427135 : Blo 1967435 4427135 := bstep (se 1 (by rfl) ⟨3320351, by rfl⟩ : syracuseStep 4427135 = 6640703) B6640703
theorem B2951423 : Blo 1967435 2951423 := bstep (se 1 (by rfl) ⟨2213567, by rfl⟩ : syracuseStep 2951423 = 4427135) B4427135
theorem B1967615 : Blo 1967435 1967615 := bstep (se 1 (by rfl) ⟨1475711, by rfl⟩ : syracuseStep 1967615 = 2951423) B2951423
theorem B2951429 : Blo 1967435 2951429 := bbase (se 4 (by rfl) ⟨276696, by rfl⟩ : syracuseStep 2951429 = 553393) (by norm_num)
theorem B1967619 : Blo 1967435 1967619 := bstep (se 1 (by rfl) ⟨1475714, by rfl⟩ : syracuseStep 1967619 = 2951429) B2951429
theorem B3320365 : Blo 1967435 3320365 := bbase (se 3 (by rfl) ⟨622568, by rfl⟩ : syracuseStep 3320365 = 1245137) (by norm_num)
theorem B4427153 : Blo 1967435 4427153 := bstep (se 2 (by rfl) ⟨1660182, by rfl⟩ : syracuseStep 4427153 = 3320365) B3320365
theorem B2951435 : Blo 1967435 2951435 := bstep (se 1 (by rfl) ⟨2213576, by rfl⟩ : syracuseStep 2951435 = 4427153) B4427153
theorem B1967623 : Blo 1967435 1967623 := bstep (se 1 (by rfl) ⟨1475717, by rfl⟩ : syracuseStep 1967623 = 2951435) B2951435
theorem B2213581 : Blo 1967435 2213581 := bbase (se 3 (by rfl) ⟨415046, by rfl⟩ : syracuseStep 2213581 = 830093) (by norm_num)
theorem B2951441 : Blo 1967435 2951441 := bstep (se 2 (by rfl) ⟨1106790, by rfl⟩ : syracuseStep 2951441 = 2213581) B2213581
theorem B1967627 : Blo 1967435 1967627 := bstep (se 1 (by rfl) ⟨1475720, by rfl⟩ : syracuseStep 1967627 = 2951441) B2951441
theorem B6640757 : Blo 1967435 6640757 := bbase (se 5 (by rfl) ⟨311285, by rfl⟩ : syracuseStep 6640757 = 622571) (by norm_num)
theorem B4427171 : Blo 1967435 4427171 := bstep (se 1 (by rfl) ⟨3320378, by rfl⟩ : syracuseStep 4427171 = 6640757) B6640757
theorem B2951447 : Blo 1967435 2951447 := bstep (se 1 (by rfl) ⟨2213585, by rfl⟩ : syracuseStep 2951447 = 4427171) B4427171
theorem B1967631 : Blo 1967435 1967631 := bstep (se 1 (by rfl) ⟨1475723, by rfl⟩ : syracuseStep 1967631 = 2951447) B2951447
theorem B2951453 : Blo 1967435 2951453 := bbase (se 3 (by rfl) ⟨553397, by rfl⟩ : syracuseStep 2951453 = 1106795) (by norm_num)
theorem B1967635 : Blo 1967435 1967635 := bstep (se 1 (by rfl) ⟨1475726, by rfl⟩ : syracuseStep 1967635 = 2951453) B2951453
theorem B4427189 : Blo 1967435 4427189 := bbase (se 5 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 4427189 = 415049) (by norm_num)
theorem B2951459 : Blo 1967435 2951459 := bstep (se 1 (by rfl) ⟨2213594, by rfl⟩ : syracuseStep 2951459 = 4427189) B4427189
theorem B1967639 : Blo 1967435 1967639 := bstep (se 1 (by rfl) ⟨1475729, by rfl⟩ : syracuseStep 1967639 = 2951459) B2951459
theorem B4202381 : Blo 1967435 4202381 := bbase (se 3 (by rfl) ⟨787946, by rfl⟩ : syracuseStep 4202381 = 1575893) (by norm_num)
theorem B11206349 : Blo 1967435 11206349 := bstep (se 3 (by rfl) ⟨2101190, by rfl⟩ : syracuseStep 11206349 = 4202381) B4202381
theorem B7470899 : Blo 1967435 7470899 := bstep (se 1 (by rfl) ⟨5603174, by rfl⟩ : syracuseStep 7470899 = 11206349) B11206349
theorem B4980599 : Blo 1967435 4980599 := bstep (se 1 (by rfl) ⟨3735449, by rfl⟩ : syracuseStep 4980599 = 7470899) B7470899
theorem B3320399 : Blo 1967435 3320399 := bstep (se 1 (by rfl) ⟨2490299, by rfl⟩ : syracuseStep 3320399 = 4980599) B4980599
theorem B2213599 : Blo 1967435 2213599 := bstep (se 1 (by rfl) ⟨1660199, by rfl⟩ : syracuseStep 2213599 = 3320399) B3320399
theorem B2951465 : Blo 1967435 2951465 := bstep (se 2 (by rfl) ⟨1106799, by rfl⟩ : syracuseStep 2951465 = 2213599) B2213599
theorem B1967643 : Blo 1967435 1967643 := bstep (se 1 (by rfl) ⟨1475732, by rfl⟩ : syracuseStep 1967643 = 2951465) B2951465
theorem B4202389 : Blo 1967435 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B5603185 : Blo 1967435 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B7470913 : Blo 1967435 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B9961217 : Blo 1967435 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B6640811 : Blo 1967435 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B4427207 : Blo 1967435 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B2951471 : Blo 1967435 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B1967647 : Blo 1967435 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B2951477 : Blo 1967435 2951477 := bbase (se 5 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 2951477 = 276701) (by norm_num)
theorem B1967651 : Blo 1967435 1967651 := bstep (se 1 (by rfl) ⟨1475738, by rfl⟩ : syracuseStep 1967651 = 2951477) B2951477
theorem B4980629 : Blo 1967435 4980629 := bbase (se 6 (by rfl) ⟨116733, by rfl⟩ : syracuseStep 4980629 = 233467) (by norm_num)
theorem B3320419 : Blo 1967435 3320419 := bstep (se 1 (by rfl) ⟨2490314, by rfl⟩ : syracuseStep 3320419 = 4980629) B4980629
theorem B4427225 : Blo 1967435 4427225 := bstep (se 2 (by rfl) ⟨1660209, by rfl⟩ : syracuseStep 4427225 = 3320419) B3320419
theorem B2951483 : Blo 1967435 2951483 := bstep (se 1 (by rfl) ⟨2213612, by rfl⟩ : syracuseStep 2951483 = 4427225) B4427225
theorem B1967655 : Blo 1967435 1967655 := bstep (se 1 (by rfl) ⟨1475741, by rfl⟩ : syracuseStep 1967655 = 2951483) B2951483
theorem B2213617 : Blo 1967435 2213617 := bbase (se 2 (by rfl) ⟨830106, by rfl⟩ : syracuseStep 2213617 = 1660213) (by norm_num)
theorem B2951489 : Blo 1967435 2951489 := bstep (se 2 (by rfl) ⟨1106808, by rfl⟩ : syracuseStep 2951489 = 2213617) B2213617
theorem B1967659 : Blo 1967435 1967659 := bstep (se 1 (by rfl) ⟨1475744, by rfl⟩ : syracuseStep 1967659 = 2951489) B2951489
theorem B43130069 : Blo 1967435 43130069 := bbase (se 7 (by rfl) ⟨505430, by rfl⟩ : syracuseStep 43130069 = 1010861) (by norm_num)
theorem B28753379 : Blo 1967435 28753379 := bstep (se 1 (by rfl) ⟨21565034, by rfl⟩ : syracuseStep 28753379 = 43130069) B43130069
theorem B19168919 : Blo 1967435 19168919 := bstep (se 1 (by rfl) ⟨14376689, by rfl⟩ : syracuseStep 19168919 = 28753379) B28753379
theorem B12779279 : Blo 1967435 12779279 := bstep (se 1 (by rfl) ⟨9584459, by rfl⟩ : syracuseStep 12779279 = 19168919) B19168919
theorem B8519519 : Blo 1967435 8519519 := bstep (se 1 (by rfl) ⟨6389639, by rfl⟩ : syracuseStep 8519519 = 12779279) B12779279
theorem B22718717 : Blo 1967435 22718717 := bstep (se 3 (by rfl) ⟨4259759, by rfl⟩ : syracuseStep 22718717 = 8519519) B8519519
theorem B15145811 : Blo 1967435 15145811 := bstep (se 1 (by rfl) ⟨11359358, by rfl⟩ : syracuseStep 15145811 = 22718717) B22718717
theorem B10097207 : Blo 1967435 10097207 := bstep (se 1 (by rfl) ⟨7572905, by rfl⟩ : syracuseStep 10097207 = 15145811) B15145811
theorem B6731471 : Blo 1967435 6731471 := bstep (se 1 (by rfl) ⟨5048603, by rfl⟩ : syracuseStep 6731471 = 10097207) B10097207
theorem B17950589 : Blo 1967435 17950589 := bstep (se 3 (by rfl) ⟨3365735, by rfl⟩ : syracuseStep 17950589 = 6731471) B6731471
theorem B11967059 : Blo 1967435 11967059 := bstep (se 1 (by rfl) ⟨8975294, by rfl⟩ : syracuseStep 11967059 = 17950589) B17950589
theorem B31912157 : Blo 1967435 31912157 := bstep (se 3 (by rfl) ⟨5983529, by rfl⟩ : syracuseStep 31912157 = 11967059) B11967059
theorem B21274771 : Blo 1967435 21274771 := bstep (se 1 (by rfl) ⟨15956078, by rfl⟩ : syracuseStep 21274771 = 31912157) B31912157
theorem B28366361 : Blo 1967435 28366361 := bstep (se 2 (by rfl) ⟨10637385, by rfl⟩ : syracuseStep 28366361 = 21274771) B21274771
theorem B18910907 : Blo 1967435 18910907 := bstep (se 1 (by rfl) ⟨14183180, by rfl⟩ : syracuseStep 18910907 = 28366361) B28366361
theorem B12607271 : Blo 1967435 12607271 := bstep (se 1 (by rfl) ⟨9455453, by rfl⟩ : syracuseStep 12607271 = 18910907) B18910907
theorem B8404847 : Blo 1967435 8404847 := bstep (se 1 (by rfl) ⟨6303635, by rfl⟩ : syracuseStep 8404847 = 12607271) B12607271
theorem B5603231 : Blo 1967435 5603231 := bstep (se 1 (by rfl) ⟨4202423, by rfl⟩ : syracuseStep 5603231 = 8404847) B8404847
theorem B3735487 : Blo 1967435 3735487 := bstep (se 1 (by rfl) ⟨2801615, by rfl⟩ : syracuseStep 3735487 = 5603231) B5603231
theorem B4980649 : Blo 1967435 4980649 := bstep (se 2 (by rfl) ⟨1867743, by rfl⟩ : syracuseStep 4980649 = 3735487) B3735487
theorem B6640865 : Blo 1967435 6640865 := bstep (se 2 (by rfl) ⟨2490324, by rfl⟩ : syracuseStep 6640865 = 4980649) B4980649
theorem B4427243 : Blo 1967435 4427243 := bstep (se 1 (by rfl) ⟨3320432, by rfl⟩ : syracuseStep 4427243 = 6640865) B6640865
theorem B2951495 : Blo 1967435 2951495 := bstep (se 1 (by rfl) ⟨2213621, by rfl⟩ : syracuseStep 2951495 = 4427243) B4427243
theorem B1967663 : Blo 1967435 1967663 := bstep (se 1 (by rfl) ⟨1475747, by rfl⟩ : syracuseStep 1967663 = 2951495) B2951495
theorem B2951501 : Blo 1967435 2951501 := bbase (se 3 (by rfl) ⟨553406, by rfl⟩ : syracuseStep 2951501 = 1106813) (by norm_num)
theorem B1967667 : Blo 1967435 1967667 := bstep (se 1 (by rfl) ⟨1475750, by rfl⟩ : syracuseStep 1967667 = 2951501) B2951501
theorem B4427261 : Blo 1967435 4427261 := bbase (se 3 (by rfl) ⟨830111, by rfl⟩ : syracuseStep 4427261 = 1660223) (by norm_num)
theorem B2951507 : Blo 1967435 2951507 := bstep (se 1 (by rfl) ⟨2213630, by rfl⟩ : syracuseStep 2951507 = 4427261) B4427261
theorem B1967671 : Blo 1967435 1967671 := bstep (se 1 (by rfl) ⟨1475753, by rfl⟩ : syracuseStep 1967671 = 2951507) B2951507
theorem B3320453 : Blo 1967435 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B2213635 : Blo 1967435 2213635 := bstep (se 1 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 2213635 = 3320453) B3320453
theorem B2951513 : Blo 1967435 2951513 := bstep (se 2 (by rfl) ⟨1106817, by rfl⟩ : syracuseStep 2951513 = 2213635) B2213635
theorem B1967675 : Blo 1967435 1967675 := bstep (se 1 (by rfl) ⟨1475756, by rfl⟩ : syracuseStep 1967675 = 2951513) B2951513
theorem B14942069 : Blo 1967435 14942069 := bbase (se 5 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 14942069 = 1400819) (by norm_num)
theorem B9961379 : Blo 1967435 9961379 := bstep (se 1 (by rfl) ⟨7471034, by rfl⟩ : syracuseStep 9961379 = 14942069) B14942069
theorem B6640919 : Blo 1967435 6640919 := bstep (se 1 (by rfl) ⟨4980689, by rfl⟩ : syracuseStep 6640919 = 9961379) B9961379
theorem B4427279 : Blo 1967435 4427279 := bstep (se 1 (by rfl) ⟨3320459, by rfl⟩ : syracuseStep 4427279 = 6640919) B6640919
theorem B2951519 : Blo 1967435 2951519 := bstep (se 1 (by rfl) ⟨2213639, by rfl⟩ : syracuseStep 2951519 = 4427279) B4427279
theorem B1967679 : Blo 1967435 1967679 := bstep (se 1 (by rfl) ⟨1475759, by rfl⟩ : syracuseStep 1967679 = 2951519) B2951519
theorem B2951525 : Blo 1967435 2951525 := bbase (se 4 (by rfl) ⟨276705, by rfl⟩ : syracuseStep 2951525 = 553411) (by norm_num)
theorem B1967683 : Blo 1967435 1967683 := bstep (se 1 (by rfl) ⟨1475762, by rfl⟩ : syracuseStep 1967683 = 2951525) B2951525
theorem B3735533 : Blo 1967435 3735533 := bbase (se 3 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 3735533 = 1400825) (by norm_num)
theorem B2490355 : Blo 1967435 2490355 := bstep (se 1 (by rfl) ⟨1867766, by rfl⟩ : syracuseStep 2490355 = 3735533) B3735533
theorem B3320473 : Blo 1967435 3320473 := bstep (se 2 (by rfl) ⟨1245177, by rfl⟩ : syracuseStep 3320473 = 2490355) B2490355
theorem B4427297 : Blo 1967435 4427297 := bstep (se 2 (by rfl) ⟨1660236, by rfl⟩ : syracuseStep 4427297 = 3320473) B3320473
theorem B2951531 : Blo 1967435 2951531 := bstep (se 1 (by rfl) ⟨2213648, by rfl⟩ : syracuseStep 2951531 = 4427297) B4427297
theorem B1967687 : Blo 1967435 1967687 := bstep (se 1 (by rfl) ⟨1475765, by rfl⟩ : syracuseStep 1967687 = 2951531) B2951531
theorem B2213653 : Blo 1967435 2213653 := bbase (se 6 (by rfl) ⟨51882, by rfl⟩ : syracuseStep 2213653 = 103765) (by norm_num)
theorem B2951537 : Blo 1967435 2951537 := bstep (se 2 (by rfl) ⟨1106826, by rfl⟩ : syracuseStep 2951537 = 2213653) B2213653
theorem B1967691 : Blo 1967435 1967691 := bstep (se 1 (by rfl) ⟨1475768, by rfl⟩ : syracuseStep 1967691 = 2951537) B2951537
theorem B2490365 : Blo 1967435 2490365 := bbase (se 3 (by rfl) ⟨466943, by rfl⟩ : syracuseStep 2490365 = 933887) (by norm_num)
theorem B6640973 : Blo 1967435 6640973 := bstep (se 3 (by rfl) ⟨1245182, by rfl⟩ : syracuseStep 6640973 = 2490365) B2490365
theorem B4427315 : Blo 1967435 4427315 := bstep (se 1 (by rfl) ⟨3320486, by rfl⟩ : syracuseStep 4427315 = 6640973) B6640973
theorem B2951543 : Blo 1967435 2951543 := bstep (se 1 (by rfl) ⟨2213657, by rfl⟩ : syracuseStep 2951543 = 4427315) B4427315
theorem B1967695 : Blo 1967435 1967695 := bstep (se 1 (by rfl) ⟨1475771, by rfl⟩ : syracuseStep 1967695 = 2951543) B2951543
theorem B2951549 : Blo 1967435 2951549 := bbase (se 3 (by rfl) ⟨553415, by rfl⟩ : syracuseStep 2951549 = 1106831) (by norm_num)
theorem B1967699 : Blo 1967435 1967699 := bstep (se 1 (by rfl) ⟨1475774, by rfl⟩ : syracuseStep 1967699 = 2951549) B2951549
theorem B4427333 : Blo 1967435 4427333 := bbase (se 4 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 4427333 = 830125) (by norm_num)
theorem B2951555 : Blo 1967435 2951555 := bstep (se 1 (by rfl) ⟨2213666, by rfl⟩ : syracuseStep 2951555 = 4427333) B4427333
theorem B1967703 : Blo 1967435 1967703 := bstep (se 1 (by rfl) ⟨1475777, by rfl⟩ : syracuseStep 1967703 = 2951555) B2951555
theorem B2363917 : Blo 1967435 2363917 := bbase (se 3 (by rfl) ⟨443234, by rfl⟩ : syracuseStep 2363917 = 886469) (by norm_num)
theorem B3151889 : Blo 1967435 3151889 := bstep (se 2 (by rfl) ⟨1181958, by rfl⟩ : syracuseStep 3151889 = 2363917) B2363917
theorem B2101259 : Blo 1967435 2101259 := bstep (se 1 (by rfl) ⟨1575944, by rfl⟩ : syracuseStep 2101259 = 3151889) B3151889
theorem B5603357 : Blo 1967435 5603357 := bstep (se 3 (by rfl) ⟨1050629, by rfl⟩ : syracuseStep 5603357 = 2101259) B2101259
theorem B3735571 : Blo 1967435 3735571 := bstep (se 1 (by rfl) ⟨2801678, by rfl⟩ : syracuseStep 3735571 = 5603357) B5603357
theorem B4980761 : Blo 1967435 4980761 := bstep (se 2 (by rfl) ⟨1867785, by rfl⟩ : syracuseStep 4980761 = 3735571) B3735571
theorem B3320507 : Blo 1967435 3320507 := bstep (se 1 (by rfl) ⟨2490380, by rfl⟩ : syracuseStep 3320507 = 4980761) B4980761
theorem B2213671 : Blo 1967435 2213671 := bstep (se 1 (by rfl) ⟨1660253, by rfl⟩ : syracuseStep 2213671 = 3320507) B3320507
theorem B2951561 : Blo 1967435 2951561 := bstep (se 2 (by rfl) ⟨1106835, by rfl⟩ : syracuseStep 2951561 = 2213671) B2213671
theorem B1967707 : Blo 1967435 1967707 := bstep (se 1 (by rfl) ⟨1475780, by rfl⟩ : syracuseStep 1967707 = 2951561) B2951561
theorem B9961541 : Blo 1967435 9961541 := bbase (se 4 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 9961541 = 1867789) (by norm_num)
theorem B6641027 : Blo 1967435 6641027 := bstep (se 1 (by rfl) ⟨4980770, by rfl⟩ : syracuseStep 6641027 = 9961541) B9961541
theorem B4427351 : Blo 1967435 4427351 := bstep (se 1 (by rfl) ⟨3320513, by rfl⟩ : syracuseStep 4427351 = 6641027) B6641027
theorem B2951567 : Blo 1967435 2951567 := bstep (se 1 (by rfl) ⟨2213675, by rfl⟩ : syracuseStep 2951567 = 4427351) B4427351
theorem B1967711 : Blo 1967435 1967711 := bstep (se 1 (by rfl) ⟨1475783, by rfl⟩ : syracuseStep 1967711 = 2951567) B2951567
theorem B2951573 : Blo 1967435 2951573 := bbase (se 6 (by rfl) ⟨69177, by rfl⟩ : syracuseStep 2951573 = 138355) (by norm_num)
theorem B1967715 : Blo 1967435 1967715 := bstep (se 1 (by rfl) ⟨1475786, by rfl⟩ : syracuseStep 1967715 = 2951573) B2951573
theorem B12954005 : Blo 1967435 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B8636003 : Blo 1967435 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5757335 : Blo 1967435 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B3838223 : Blo 1967435 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B10235261 : Blo 1967435 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B6823507 : Blo 1967435 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B9098009 : Blo 1967435 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B6065339 : Blo 1967435 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B16174237 : Blo 1967435 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B21565649 : Blo 1967435 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B14377099 : Blo 1967435 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B19169465 : Blo 1967435 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B51118573 : Blo 1967435 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B68158097 : Blo 1967435 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B45438731 : Blo 1967435 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B30292487 : Blo 1967435 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B20194991 : Blo 1967435 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B13463327 : Blo 1967435 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B8975551 : Blo 1967435 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B11967401 : Blo 1967435 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B7978267 : Blo 1967435 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B10637689 : Blo 1967435 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B14183585 : Blo 1967435 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B9455723 : Blo 1967435 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B6303815 : Blo 1967435 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B4202543 : Blo 1967435 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B11206781 : Blo 1967435 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B7471187 : Blo 1967435 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B4980791 : Blo 1967435 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B3320527 : Blo 1967435 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B4427369 : Blo 1967435 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B2951579 : Blo 1967435 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B1967719 : Blo 1967435 1967719 := bstep (se 1 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 1967719 = 2951579) B2951579
theorem B2213689 : Blo 1967435 2213689 := bbase (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) (by norm_num)
theorem B2951585 : Blo 1967435 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B1967723 : Blo 1967435 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B5603413 : Blo 1967435 5603413 := bbase (se 8 (by rfl) ⟨32832, by rfl⟩ : syracuseStep 5603413 = 65665) (by norm_num)
theorem B7471217 : Blo 1967435 7471217 := bstep (se 2 (by rfl) ⟨2801706, by rfl⟩ : syracuseStep 7471217 = 5603413) B5603413
theorem B4980811 : Blo 1967435 4980811 := bstep (se 1 (by rfl) ⟨3735608, by rfl⟩ : syracuseStep 4980811 = 7471217) B7471217
theorem B6641081 : Blo 1967435 6641081 := bstep (se 2 (by rfl) ⟨2490405, by rfl⟩ : syracuseStep 6641081 = 4980811) B4980811
theorem B4427387 : Blo 1967435 4427387 := bstep (se 1 (by rfl) ⟨3320540, by rfl⟩ : syracuseStep 4427387 = 6641081) B6641081
theorem B2951591 : Blo 1967435 2951591 := bstep (se 1 (by rfl) ⟨2213693, by rfl⟩ : syracuseStep 2951591 = 4427387) B4427387
theorem B1967727 : Blo 1967435 1967727 := bstep (se 1 (by rfl) ⟨1475795, by rfl⟩ : syracuseStep 1967727 = 2951591) B2951591
theorem B2951597 : Blo 1967435 2951597 := bbase (se 3 (by rfl) ⟨553424, by rfl⟩ : syracuseStep 2951597 = 1106849) (by norm_num)
theorem B1967731 : Blo 1967435 1967731 := bstep (se 1 (by rfl) ⟨1475798, by rfl⟩ : syracuseStep 1967731 = 2951597) B2951597
theorem B4427405 : Blo 1967435 4427405 := bbase (se 3 (by rfl) ⟨830138, by rfl⟩ : syracuseStep 4427405 = 1660277) (by norm_num)
theorem B2951603 : Blo 1967435 2951603 := bstep (se 1 (by rfl) ⟨2213702, by rfl⟩ : syracuseStep 2951603 = 4427405) B4427405
theorem B1967735 : Blo 1967435 1967735 := bstep (se 1 (by rfl) ⟨1475801, by rfl⟩ : syracuseStep 1967735 = 2951603) B2951603
theorem B2490421 : Blo 1967435 2490421 := bbase (se 5 (by rfl) ⟨116738, by rfl⟩ : syracuseStep 2490421 = 233477) (by norm_num)
theorem B3320561 : Blo 1967435 3320561 := bstep (se 2 (by rfl) ⟨1245210, by rfl⟩ : syracuseStep 3320561 = 2490421) B2490421
theorem B2213707 : Blo 1967435 2213707 := bstep (se 1 (by rfl) ⟨1660280, by rfl⟩ : syracuseStep 2213707 = 3320561) B3320561
theorem B2951609 : Blo 1967435 2951609 := bstep (se 2 (by rfl) ⟨1106853, by rfl⟩ : syracuseStep 2951609 = 2213707) B2213707
theorem B1967739 : Blo 1967435 1967739 := bstep (se 1 (by rfl) ⟨1475804, by rfl⟩ : syracuseStep 1967739 = 2951609) B2951609
theorem B28367509 : Blo 1967435 28367509 := bbase (se 6 (by rfl) ⟨664863, by rfl⟩ : syracuseStep 28367509 = 1329727) (by norm_num)
theorem B37823345 : Blo 1967435 37823345 := bstep (se 2 (by rfl) ⟨14183754, by rfl⟩ : syracuseStep 37823345 = 28367509) B28367509
theorem B25215563 : Blo 1967435 25215563 := bstep (se 1 (by rfl) ⟨18911672, by rfl⟩ : syracuseStep 25215563 = 37823345) B37823345
theorem B16810375 : Blo 1967435 16810375 := bstep (se 1 (by rfl) ⟨12607781, by rfl⟩ : syracuseStep 16810375 = 25215563) B25215563
theorem B22413833 : Blo 1967435 22413833 := bstep (se 2 (by rfl) ⟨8405187, by rfl⟩ : syracuseStep 22413833 = 16810375) B16810375
theorem B14942555 : Blo 1967435 14942555 := bstep (se 1 (by rfl) ⟨11206916, by rfl⟩ : syracuseStep 14942555 = 22413833) B22413833
theorem B9961703 : Blo 1967435 9961703 := bstep (se 1 (by rfl) ⟨7471277, by rfl⟩ : syracuseStep 9961703 = 14942555) B14942555
theorem B6641135 : Blo 1967435 6641135 := bstep (se 1 (by rfl) ⟨4980851, by rfl⟩ : syracuseStep 6641135 = 9961703) B9961703
theorem B4427423 : Blo 1967435 4427423 := bstep (se 1 (by rfl) ⟨3320567, by rfl⟩ : syracuseStep 4427423 = 6641135) B6641135
theorem B2951615 : Blo 1967435 2951615 := bstep (se 1 (by rfl) ⟨2213711, by rfl⟩ : syracuseStep 2951615 = 4427423) B4427423
theorem B1967743 : Blo 1967435 1967743 := bstep (se 1 (by rfl) ⟨1475807, by rfl⟩ : syracuseStep 1967743 = 2951615) B2951615
theorem B2951621 : Blo 1967435 2951621 := bbase (se 4 (by rfl) ⟨276714, by rfl⟩ : syracuseStep 2951621 = 553429) (by norm_num)
theorem B1967747 : Blo 1967435 1967747 := bstep (se 1 (by rfl) ⟨1475810, by rfl⟩ : syracuseStep 1967747 = 2951621) B2951621
theorem B3320581 : Blo 1967435 3320581 := bbase (se 4 (by rfl) ⟨311304, by rfl⟩ : syracuseStep 3320581 = 622609) (by norm_num)
theorem B4427441 : Blo 1967435 4427441 := bstep (se 2 (by rfl) ⟨1660290, by rfl⟩ : syracuseStep 4427441 = 3320581) B3320581
theorem B2951627 : Blo 1967435 2951627 := bstep (se 1 (by rfl) ⟨2213720, by rfl⟩ : syracuseStep 2951627 = 4427441) B4427441
theorem B1967751 : Blo 1967435 1967751 := bstep (se 1 (by rfl) ⟨1475813, by rfl⟩ : syracuseStep 1967751 = 2951627) B2951627
theorem B2213725 : Blo 1967435 2213725 := bbase (se 3 (by rfl) ⟨415073, by rfl⟩ : syracuseStep 2213725 = 830147) (by norm_num)
theorem B2951633 : Blo 1967435 2951633 := bstep (se 2 (by rfl) ⟨1106862, by rfl⟩ : syracuseStep 2951633 = 2213725) B2213725
theorem B1967755 : Blo 1967435 1967755 := bstep (se 1 (by rfl) ⟨1475816, by rfl⟩ : syracuseStep 1967755 = 2951633) B2951633
theorem B6641189 : Blo 1967435 6641189 := bbase (se 4 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 6641189 = 1245223) (by norm_num)
theorem B4427459 : Blo 1967435 4427459 := bstep (se 1 (by rfl) ⟨3320594, by rfl⟩ : syracuseStep 4427459 = 6641189) B6641189
theorem B2951639 : Blo 1967435 2951639 := bstep (se 1 (by rfl) ⟨2213729, by rfl⟩ : syracuseStep 2951639 = 4427459) B4427459
theorem B1967759 : Blo 1967435 1967759 := bstep (se 1 (by rfl) ⟨1475819, by rfl⟩ : syracuseStep 1967759 = 2951639) B2951639
theorem B2951645 : Blo 1967435 2951645 := bbase (se 3 (by rfl) ⟨553433, by rfl⟩ : syracuseStep 2951645 = 1106867) (by norm_num)
theorem B1967763 : Blo 1967435 1967763 := bstep (se 1 (by rfl) ⟨1475822, by rfl⟩ : syracuseStep 1967763 = 2951645) B2951645
theorem B4427477 : Blo 1967435 4427477 := bbase (se 7 (by rfl) ⟨51884, by rfl⟩ : syracuseStep 4427477 = 103769) (by norm_num)
theorem B2951651 : Blo 1967435 2951651 := bstep (se 1 (by rfl) ⟨2213738, by rfl⟩ : syracuseStep 2951651 = 4427477) B4427477
theorem B1967767 : Blo 1967435 1967767 := bstep (se 1 (by rfl) ⟨1475825, by rfl⟩ : syracuseStep 1967767 = 2951651) B2951651
theorem B2659493 : Blo 1967435 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B7091981 : Blo 1967435 7091981 := bstep (se 3 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 7091981 = 2659493) B2659493
theorem B4727987 : Blo 1967435 4727987 := bstep (se 1 (by rfl) ⟨3545990, by rfl⟩ : syracuseStep 4727987 = 7091981) B7091981
theorem B3151991 : Blo 1967435 3151991 := bstep (se 1 (by rfl) ⟨2363993, by rfl⟩ : syracuseStep 3151991 = 4727987) B4727987
theorem B8405309 : Blo 1967435 8405309 := bstep (se 3 (by rfl) ⟨1575995, by rfl⟩ : syracuseStep 8405309 = 3151991) B3151991
theorem B5603539 : Blo 1967435 5603539 := bstep (se 1 (by rfl) ⟨4202654, by rfl⟩ : syracuseStep 5603539 = 8405309) B8405309
theorem B7471385 : Blo 1967435 7471385 := bstep (se 2 (by rfl) ⟨2801769, by rfl⟩ : syracuseStep 7471385 = 5603539) B5603539
theorem B4980923 : Blo 1967435 4980923 := bstep (se 1 (by rfl) ⟨3735692, by rfl⟩ : syracuseStep 4980923 = 7471385) B7471385
theorem B3320615 : Blo 1967435 3320615 := bstep (se 1 (by rfl) ⟨2490461, by rfl⟩ : syracuseStep 3320615 = 4980923) B4980923
theorem B2213743 : Blo 1967435 2213743 := bstep (se 1 (by rfl) ⟨1660307, by rfl⟩ : syracuseStep 2213743 = 3320615) B3320615
theorem B2951657 : Blo 1967435 2951657 := bstep (se 2 (by rfl) ⟨1106871, by rfl⟩ : syracuseStep 2951657 = 2213743) B2213743
theorem B1967771 : Blo 1967435 1967771 := bstep (se 1 (by rfl) ⟨1475828, by rfl⟩ : syracuseStep 1967771 = 2951657) B2951657
theorem B8520005 : Blo 1967435 8520005 := bbase (se 4 (by rfl) ⟨798750, by rfl⟩ : syracuseStep 8520005 = 1597501) (by norm_num)
theorem B22720013 : Blo 1967435 22720013 := bstep (se 3 (by rfl) ⟨4260002, by rfl⟩ : syracuseStep 22720013 = 8520005) B8520005
theorem B15146675 : Blo 1967435 15146675 := bstep (se 1 (by rfl) ⟨11360006, by rfl⟩ : syracuseStep 15146675 = 22720013) B22720013
theorem B10097783 : Blo 1967435 10097783 := bstep (se 1 (by rfl) ⟨7573337, by rfl⟩ : syracuseStep 10097783 = 15146675) B15146675
theorem B6731855 : Blo 1967435 6731855 := bstep (se 1 (by rfl) ⟨5048891, by rfl⟩ : syracuseStep 6731855 = 10097783) B10097783
theorem B4487903 : Blo 1967435 4487903 := bstep (se 1 (by rfl) ⟨3365927, by rfl⟩ : syracuseStep 4487903 = 6731855) B6731855
theorem B2991935 : Blo 1967435 2991935 := bstep (se 1 (by rfl) ⟨2243951, by rfl⟩ : syracuseStep 2991935 = 4487903) B4487903
theorem B7978493 : Blo 1967435 7978493 := bstep (se 3 (by rfl) ⟨1495967, by rfl⟩ : syracuseStep 7978493 = 2991935) B2991935
theorem B5318995 : Blo 1967435 5318995 := bstep (se 1 (by rfl) ⟨3989246, by rfl⟩ : syracuseStep 5318995 = 7978493) B7978493
theorem B7091993 : Blo 1967435 7091993 := bstep (se 2 (by rfl) ⟨2659497, by rfl⟩ : syracuseStep 7091993 = 5318995) B5318995
theorem B18911981 : Blo 1967435 18911981 := bstep (se 3 (by rfl) ⟨3545996, by rfl⟩ : syracuseStep 18911981 = 7091993) B7091993
theorem B12607987 : Blo 1967435 12607987 := bstep (se 1 (by rfl) ⟨9455990, by rfl⟩ : syracuseStep 12607987 = 18911981) B18911981
theorem B16810649 : Blo 1967435 16810649 := bstep (se 2 (by rfl) ⟨6303993, by rfl⟩ : syracuseStep 16810649 = 12607987) B12607987
theorem B11207099 : Blo 1967435 11207099 := bstep (se 1 (by rfl) ⟨8405324, by rfl⟩ : syracuseStep 11207099 = 16810649) B16810649
theorem B7471399 : Blo 1967435 7471399 := bstep (se 1 (by rfl) ⟨5603549, by rfl⟩ : syracuseStep 7471399 = 11207099) B11207099
theorem B9961865 : Blo 1967435 9961865 := bstep (se 2 (by rfl) ⟨3735699, by rfl⟩ : syracuseStep 9961865 = 7471399) B7471399
theorem B6641243 : Blo 1967435 6641243 := bstep (se 1 (by rfl) ⟨4980932, by rfl⟩ : syracuseStep 6641243 = 9961865) B9961865
theorem B4427495 : Blo 1967435 4427495 := bstep (se 1 (by rfl) ⟨3320621, by rfl⟩ : syracuseStep 4427495 = 6641243) B6641243
theorem B2951663 : Blo 1967435 2951663 := bstep (se 1 (by rfl) ⟨2213747, by rfl⟩ : syracuseStep 2951663 = 4427495) B4427495
theorem B1967775 : Blo 1967435 1967775 := bstep (se 1 (by rfl) ⟨1475831, by rfl⟩ : syracuseStep 1967775 = 2951663) B2951663
theorem B2951669 : Blo 1967435 2951669 := bbase (se 5 (by rfl) ⟨138359, by rfl⟩ : syracuseStep 2951669 = 276719) (by norm_num)
theorem B1967779 : Blo 1967435 1967779 := bstep (se 1 (by rfl) ⟨1475834, by rfl⟩ : syracuseStep 1967779 = 2951669) B2951669
theorem B5603573 : Blo 1967435 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B3735715 : Blo 1967435 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B4980953 : Blo 1967435 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B3320635 : Blo 1967435 3320635 := bstep (se 1 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 3320635 = 4980953) B4980953
theorem B4427513 : Blo 1967435 4427513 := bstep (se 2 (by rfl) ⟨1660317, by rfl⟩ : syracuseStep 4427513 = 3320635) B3320635
theorem B2951675 : Blo 1967435 2951675 := bstep (se 1 (by rfl) ⟨2213756, by rfl⟩ : syracuseStep 2951675 = 4427513) B4427513
theorem B1967783 : Blo 1967435 1967783 := bstep (se 1 (by rfl) ⟨1475837, by rfl⟩ : syracuseStep 1967783 = 2951675) B2951675
theorem B2213761 : Blo 1967435 2213761 := bbase (se 2 (by rfl) ⟨830160, by rfl⟩ : syracuseStep 2213761 = 1660321) (by norm_num)
theorem B2951681 : Blo 1967435 2951681 := bstep (se 2 (by rfl) ⟨1106880, by rfl⟩ : syracuseStep 2951681 = 2213761) B2213761
theorem B1967787 : Blo 1967435 1967787 := bstep (se 1 (by rfl) ⟨1475840, by rfl⟩ : syracuseStep 1967787 = 2951681) B2951681
theorem B4980973 : Blo 1967435 4980973 := bbase (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) (by norm_num)
theorem B6641297 : Blo 1967435 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B4427531 : Blo 1967435 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B2951687 : Blo 1967435 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B1967791 : Blo 1967435 1967791 := bstep (se 1 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 1967791 = 2951687) B2951687
theorem B2951693 : Blo 1967435 2951693 := bbase (se 3 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 2951693 = 1106885) (by norm_num)
theorem B1967795 : Blo 1967435 1967795 := bstep (se 1 (by rfl) ⟨1475846, by rfl⟩ : syracuseStep 1967795 = 2951693) B2951693
theorem B4427549 : Blo 1967435 4427549 := bbase (se 3 (by rfl) ⟨830165, by rfl⟩ : syracuseStep 4427549 = 1660331) (by norm_num)
theorem B2951699 : Blo 1967435 2951699 := bstep (se 1 (by rfl) ⟨2213774, by rfl⟩ : syracuseStep 2951699 = 4427549) B4427549
theorem B1967799 : Blo 1967435 1967799 := bstep (se 1 (by rfl) ⟨1475849, by rfl⟩ : syracuseStep 1967799 = 2951699) B2951699
theorem B3320669 : Blo 1967435 3320669 := bbase (se 3 (by rfl) ⟨622625, by rfl⟩ : syracuseStep 3320669 = 1245251) (by norm_num)
theorem B2213779 : Blo 1967435 2213779 := bstep (se 1 (by rfl) ⟨1660334, by rfl⟩ : syracuseStep 2213779 = 3320669) B3320669
theorem B2951705 : Blo 1967435 2951705 := bstep (se 2 (by rfl) ⟨1106889, by rfl⟩ : syracuseStep 2951705 = 2213779) B2213779
theorem B1967803 : Blo 1967435 1967803 := bstep (se 1 (by rfl) ⟨1475852, by rfl⟩ : syracuseStep 1967803 = 2951705) B2951705
theorem B8405461 : Blo 1967435 8405461 := bbase (se 7 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 8405461 = 197003) (by norm_num)
theorem B11207281 : Blo 1967435 11207281 := bstep (se 2 (by rfl) ⟨4202730, by rfl⟩ : syracuseStep 11207281 = 8405461) B8405461
theorem B14943041 : Blo 1967435 14943041 := bstep (se 2 (by rfl) ⟨5603640, by rfl⟩ : syracuseStep 14943041 = 11207281) B11207281
theorem B9962027 : Blo 1967435 9962027 := bstep (se 1 (by rfl) ⟨7471520, by rfl⟩ : syracuseStep 9962027 = 14943041) B14943041
theorem B6641351 : Blo 1967435 6641351 := bstep (se 1 (by rfl) ⟨4981013, by rfl⟩ : syracuseStep 6641351 = 9962027) B9962027
theorem B4427567 : Blo 1967435 4427567 := bstep (se 1 (by rfl) ⟨3320675, by rfl⟩ : syracuseStep 4427567 = 6641351) B6641351
theorem B2951711 : Blo 1967435 2951711 := bstep (se 1 (by rfl) ⟨2213783, by rfl⟩ : syracuseStep 2951711 = 4427567) B4427567
theorem B1967807 : Blo 1967435 1967807 := bstep (se 1 (by rfl) ⟨1475855, by rfl⟩ : syracuseStep 1967807 = 2951711) B2951711
theorem B2951717 : Blo 1967435 2951717 := bbase (se 4 (by rfl) ⟨276723, by rfl⟩ : syracuseStep 2951717 = 553447) (by norm_num)
theorem B1967811 : Blo 1967435 1967811 := bstep (se 1 (by rfl) ⟨1475858, by rfl⟩ : syracuseStep 1967811 = 2951717) B2951717
theorem B2490517 : Blo 1967435 2490517 := bbase (se 6 (by rfl) ⟨58371, by rfl⟩ : syracuseStep 2490517 = 116743) (by norm_num)
theorem B3320689 : Blo 1967435 3320689 := bstep (se 2 (by rfl) ⟨1245258, by rfl⟩ : syracuseStep 3320689 = 2490517) B2490517
theorem B4427585 : Blo 1967435 4427585 := bstep (se 2 (by rfl) ⟨1660344, by rfl⟩ : syracuseStep 4427585 = 3320689) B3320689
theorem B2951723 : Blo 1967435 2951723 := bstep (se 1 (by rfl) ⟨2213792, by rfl⟩ : syracuseStep 2951723 = 4427585) B4427585
theorem B1967815 : Blo 1967435 1967815 := bstep (se 1 (by rfl) ⟨1475861, by rfl⟩ : syracuseStep 1967815 = 2951723) B2951723
theorem B2213797 : Blo 1967435 2213797 := bbase (se 4 (by rfl) ⟨207543, by rfl⟩ : syracuseStep 2213797 = 415087) (by norm_num)
theorem B2951729 : Blo 1967435 2951729 := bstep (se 2 (by rfl) ⟨1106898, by rfl⟩ : syracuseStep 2951729 = 2213797) B2213797
theorem B1967819 : Blo 1967435 1967819 := bstep (se 1 (by rfl) ⟨1475864, by rfl⟩ : syracuseStep 1967819 = 2951729) B2951729
theorem B4792621 : Blo 1967435 4792621 := bbase (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) (by norm_num)
theorem B6390161 : Blo 1967435 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B4260107 : Blo 1967435 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B2840071 : Blo 1967435 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B3786761 : Blo 1967435 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B10098029 : Blo 1967435 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B6732019 : Blo 1967435 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B8976025 : Blo 1967435 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B47872133 : Blo 1967435 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B31914755 : Blo 1967435 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B21276503 : Blo 1967435 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B14184335 : Blo 1967435 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B9456223 : Blo 1967435 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B12608297 : Blo 1967435 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B8405531 : Blo 1967435 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B5603687 : Blo 1967435 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B3735791 : Blo 1967435 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B2490527 : Blo 1967435 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B6641405 : Blo 1967435 6641405 := bstep (se 3 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 6641405 = 2490527) B2490527
theorem B4427603 : Blo 1967435 4427603 := bstep (se 1 (by rfl) ⟨3320702, by rfl⟩ : syracuseStep 4427603 = 6641405) B6641405
theorem B2951735 : Blo 1967435 2951735 := bstep (se 1 (by rfl) ⟨2213801, by rfl⟩ : syracuseStep 2951735 = 4427603) B4427603
theorem B1967823 : Blo 1967435 1967823 := bstep (se 1 (by rfl) ⟨1475867, by rfl⟩ : syracuseStep 1967823 = 2951735) B2951735
theorem B2951741 : Blo 1967435 2951741 := bbase (se 3 (by rfl) ⟨553451, by rfl⟩ : syracuseStep 2951741 = 1106903) (by norm_num)
theorem B1967827 : Blo 1967435 1967827 := bstep (se 1 (by rfl) ⟨1475870, by rfl⟩ : syracuseStep 1967827 = 2951741) B2951741
theorem B4427621 : Blo 1967435 4427621 := bbase (se 4 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 4427621 = 830179) (by norm_num)
theorem B2951747 : Blo 1967435 2951747 := bstep (se 1 (by rfl) ⟨2213810, by rfl⟩ : syracuseStep 2951747 = 4427621) B4427621
theorem B1967831 : Blo 1967435 1967831 := bstep (se 1 (by rfl) ⟨1475873, by rfl⟩ : syracuseStep 1967831 = 2951747) B2951747
theorem B4981085 : Blo 1967435 4981085 := bbase (se 3 (by rfl) ⟨933953, by rfl⟩ : syracuseStep 4981085 = 1867907) (by norm_num)
theorem B3320723 : Blo 1967435 3320723 := bstep (se 1 (by rfl) ⟨2490542, by rfl⟩ : syracuseStep 3320723 = 4981085) B4981085
theorem B2213815 : Blo 1967435 2213815 := bstep (se 1 (by rfl) ⟨1660361, by rfl⟩ : syracuseStep 2213815 = 3320723) B3320723
theorem B2951753 : Blo 1967435 2951753 := bstep (se 2 (by rfl) ⟨1106907, by rfl⟩ : syracuseStep 2951753 = 2213815) B2213815
theorem B1967835 : Blo 1967435 1967835 := bstep (se 1 (by rfl) ⟨1475876, by rfl⟩ : syracuseStep 1967835 = 2951753) B2951753
theorem B3735821 : Blo 1967435 3735821 := bbase (se 3 (by rfl) ⟨700466, by rfl⟩ : syracuseStep 3735821 = 1400933) (by norm_num)
theorem B9962189 : Blo 1967435 9962189 := bstep (se 3 (by rfl) ⟨1867910, by rfl⟩ : syracuseStep 9962189 = 3735821) B3735821
theorem B6641459 : Blo 1967435 6641459 := bstep (se 1 (by rfl) ⟨4981094, by rfl⟩ : syracuseStep 6641459 = 9962189) B9962189
theorem B4427639 : Blo 1967435 4427639 := bstep (se 1 (by rfl) ⟨3320729, by rfl⟩ : syracuseStep 4427639 = 6641459) B6641459
theorem B2951759 : Blo 1967435 2951759 := bstep (se 1 (by rfl) ⟨2213819, by rfl⟩ : syracuseStep 2951759 = 4427639) B4427639
theorem B1967839 : Blo 1967435 1967839 := bstep (se 1 (by rfl) ⟨1475879, by rfl⟩ : syracuseStep 1967839 = 2951759) B2951759
theorem B2951765 : Blo 1967435 2951765 := bbase (se 8 (by rfl) ⟨17295, by rfl⟩ : syracuseStep 2951765 = 34591) (by norm_num)
theorem B1967843 : Blo 1967435 1967843 := bstep (se 1 (by rfl) ⟨1475882, by rfl⟩ : syracuseStep 1967843 = 2951765) B2951765
theorem B11968181 : Blo 1967435 11968181 := bbase (se 5 (by rfl) ⟨561008, by rfl⟩ : syracuseStep 11968181 = 1122017) (by norm_num)
theorem B7978787 : Blo 1967435 7978787 := bstep (se 1 (by rfl) ⟨5984090, by rfl⟩ : syracuseStep 7978787 = 11968181) B11968181
theorem B5319191 : Blo 1967435 5319191 := bstep (se 1 (by rfl) ⟨3989393, by rfl⟩ : syracuseStep 5319191 = 7978787) B7978787
theorem B3546127 : Blo 1967435 3546127 := bstep (se 1 (by rfl) ⟨2659595, by rfl⟩ : syracuseStep 3546127 = 5319191) B5319191
theorem B4728169 : Blo 1967435 4728169 := bstep (se 2 (by rfl) ⟨1773063, by rfl⟩ : syracuseStep 4728169 = 3546127) B3546127
theorem B6304225 : Blo 1967435 6304225 := bstep (se 2 (by rfl) ⟨2364084, by rfl⟩ : syracuseStep 6304225 = 4728169) B4728169
theorem B8405633 : Blo 1967435 8405633 := bstep (se 2 (by rfl) ⟨3152112, by rfl⟩ : syracuseStep 8405633 = 6304225) B6304225
theorem B5603755 : Blo 1967435 5603755 := bstep (se 1 (by rfl) ⟨4202816, by rfl⟩ : syracuseStep 5603755 = 8405633) B8405633
theorem B7471673 : Blo 1967435 7471673 := bstep (se 2 (by rfl) ⟨2801877, by rfl⟩ : syracuseStep 7471673 = 5603755) B5603755
theorem B4981115 : Blo 1967435 4981115 := bstep (se 1 (by rfl) ⟨3735836, by rfl⟩ : syracuseStep 4981115 = 7471673) B7471673
theorem B3320743 : Blo 1967435 3320743 := bstep (se 1 (by rfl) ⟨2490557, by rfl⟩ : syracuseStep 3320743 = 4981115) B4981115
theorem B4427657 : Blo 1967435 4427657 := bstep (se 2 (by rfl) ⟨1660371, by rfl⟩ : syracuseStep 4427657 = 3320743) B3320743
theorem B2951771 : Blo 1967435 2951771 := bstep (se 1 (by rfl) ⟨2213828, by rfl⟩ : syracuseStep 2951771 = 4427657) B4427657
theorem B1967847 : Blo 1967435 1967847 := bstep (se 1 (by rfl) ⟨1475885, by rfl⟩ : syracuseStep 1967847 = 2951771) B2951771
theorem B2213833 : Blo 1967435 2213833 := bbase (se 2 (by rfl) ⟨830187, by rfl⟩ : syracuseStep 2213833 = 1660375) (by norm_num)
theorem B2951777 : Blo 1967435 2951777 := bstep (se 2 (by rfl) ⟨1106916, by rfl⟩ : syracuseStep 2951777 = 2213833) B2213833
theorem B1967851 : Blo 1967435 1967851 := bstep (se 1 (by rfl) ⟨1475888, by rfl⟩ : syracuseStep 1967851 = 2951777) B2951777
theorem B3152125 : Blo 1967435 3152125 := bbase (se 3 (by rfl) ⟨591023, by rfl⟩ : syracuseStep 3152125 = 1182047) (by norm_num)
theorem B16811333 : Blo 1967435 16811333 := bstep (se 4 (by rfl) ⟨1576062, by rfl⟩ : syracuseStep 16811333 = 3152125) B3152125
theorem B11207555 : Blo 1967435 11207555 := bstep (se 1 (by rfl) ⟨8405666, by rfl⟩ : syracuseStep 11207555 = 16811333) B16811333
theorem B7471703 : Blo 1967435 7471703 := bstep (se 1 (by rfl) ⟨5603777, by rfl⟩ : syracuseStep 7471703 = 11207555) B11207555
theorem B4981135 : Blo 1967435 4981135 := bstep (se 1 (by rfl) ⟨3735851, by rfl⟩ : syracuseStep 4981135 = 7471703) B7471703
theorem B6641513 : Blo 1967435 6641513 := bstep (se 2 (by rfl) ⟨2490567, by rfl⟩ : syracuseStep 6641513 = 4981135) B4981135
theorem B4427675 : Blo 1967435 4427675 := bstep (se 1 (by rfl) ⟨3320756, by rfl⟩ : syracuseStep 4427675 = 6641513) B6641513
theorem B2951783 : Blo 1967435 2951783 := bstep (se 1 (by rfl) ⟨2213837, by rfl⟩ : syracuseStep 2951783 = 4427675) B4427675
theorem B1967855 : Blo 1967435 1967855 := bstep (se 1 (by rfl) ⟨1475891, by rfl⟩ : syracuseStep 1967855 = 2951783) B2951783
theorem B2951789 : Blo 1967435 2951789 := bbase (se 3 (by rfl) ⟨553460, by rfl⟩ : syracuseStep 2951789 = 1106921) (by norm_num)
theorem B1967859 : Blo 1967435 1967859 := bstep (se 1 (by rfl) ⟨1475894, by rfl⟩ : syracuseStep 1967859 = 2951789) B2951789
theorem B4427693 : Blo 1967435 4427693 := bbase (se 3 (by rfl) ⟨830192, by rfl⟩ : syracuseStep 4427693 = 1660385) (by norm_num)
theorem B2951795 : Blo 1967435 2951795 := bstep (se 1 (by rfl) ⟨2213846, by rfl⟩ : syracuseStep 2951795 = 4427693) B4427693
theorem B1967863 : Blo 1967435 1967863 := bstep (se 1 (by rfl) ⟨1475897, by rfl⟩ : syracuseStep 1967863 = 2951795) B2951795
theorem B5603813 : Blo 1967435 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B3735875 : Blo 1967435 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B2490583 : Blo 1967435 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B3320777 : Blo 1967435 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B2213851 : Blo 1967435 2213851 := bstep (se 1 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 2213851 = 3320777) B3320777
theorem B2951801 : Blo 1967435 2951801 := bstep (se 2 (by rfl) ⟨1106925, by rfl⟩ : syracuseStep 2951801 = 2213851) B2213851
theorem B1967867 : Blo 1967435 1967867 := bstep (se 1 (by rfl) ⟨1475900, by rfl⟩ : syracuseStep 1967867 = 2951801) B2951801
theorem B2244061 : Blo 1967435 2244061 := bbase (se 3 (by rfl) ⟨420761, by rfl⟩ : syracuseStep 2244061 = 841523) (by norm_num)
theorem B2992081 : Blo 1967435 2992081 := bstep (se 2 (by rfl) ⟨1122030, by rfl⟩ : syracuseStep 2992081 = 2244061) B2244061
theorem B3989441 : Blo 1967435 3989441 := bstep (se 2 (by rfl) ⟨1496040, by rfl⟩ : syracuseStep 3989441 = 2992081) B2992081
theorem B2659627 : Blo 1967435 2659627 := bstep (se 1 (by rfl) ⟨1994720, by rfl⟩ : syracuseStep 2659627 = 3989441) B3989441
theorem B14184677 : Blo 1967435 14184677 := bstep (se 4 (by rfl) ⟨1329813, by rfl⟩ : syracuseStep 14184677 = 2659627) B2659627
theorem B37825805 : Blo 1967435 37825805 := bstep (se 3 (by rfl) ⟨7092338, by rfl⟩ : syracuseStep 37825805 = 14184677) B14184677
theorem B25217203 : Blo 1967435 25217203 := bstep (se 1 (by rfl) ⟨18912902, by rfl⟩ : syracuseStep 25217203 = 37825805) B37825805
theorem B33622937 : Blo 1967435 33622937 := bstep (se 2 (by rfl) ⟨12608601, by rfl⟩ : syracuseStep 33622937 = 25217203) B25217203
theorem B22415291 : Blo 1967435 22415291 := bstep (se 1 (by rfl) ⟨16811468, by rfl⟩ : syracuseStep 22415291 = 33622937) B33622937
theorem B14943527 : Blo 1967435 14943527 := bstep (se 1 (by rfl) ⟨11207645, by rfl⟩ : syracuseStep 14943527 = 22415291) B22415291
theorem B9962351 : Blo 1967435 9962351 := bstep (se 1 (by rfl) ⟨7471763, by rfl⟩ : syracuseStep 9962351 = 14943527) B14943527
theorem B6641567 : Blo 1967435 6641567 := bstep (se 1 (by rfl) ⟨4981175, by rfl⟩ : syracuseStep 6641567 = 9962351) B9962351
theorem B4427711 : Blo 1967435 4427711 := bstep (se 1 (by rfl) ⟨3320783, by rfl⟩ : syracuseStep 4427711 = 6641567) B6641567
theorem B2951807 : Blo 1967435 2951807 := bstep (se 1 (by rfl) ⟨2213855, by rfl⟩ : syracuseStep 2951807 = 4427711) B4427711
theorem B1967871 : Blo 1967435 1967871 := bstep (se 1 (by rfl) ⟨1475903, by rfl⟩ : syracuseStep 1967871 = 2951807) B2951807
theorem B2951813 : Blo 1967435 2951813 := bbase (se 4 (by rfl) ⟨276732, by rfl⟩ : syracuseStep 2951813 = 553465) (by norm_num)
theorem B1967875 : Blo 1967435 1967875 := bstep (se 1 (by rfl) ⟨1475906, by rfl⟩ : syracuseStep 1967875 = 2951813) B2951813
theorem B3320797 : Blo 1967435 3320797 := bbase (se 3 (by rfl) ⟨622649, by rfl⟩ : syracuseStep 3320797 = 1245299) (by norm_num)
theorem B4427729 : Blo 1967435 4427729 := bstep (se 2 (by rfl) ⟨1660398, by rfl⟩ : syracuseStep 4427729 = 3320797) B3320797
theorem B2951819 : Blo 1967435 2951819 := bstep (se 1 (by rfl) ⟨2213864, by rfl⟩ : syracuseStep 2951819 = 4427729) B4427729
theorem B1967879 : Blo 1967435 1967879 := bstep (se 1 (by rfl) ⟨1475909, by rfl⟩ : syracuseStep 1967879 = 2951819) B2951819
theorem B2213869 : Blo 1967435 2213869 := bbase (se 3 (by rfl) ⟨415100, by rfl⟩ : syracuseStep 2213869 = 830201) (by norm_num)
theorem B2951825 : Blo 1967435 2951825 := bstep (se 2 (by rfl) ⟨1106934, by rfl⟩ : syracuseStep 2951825 = 2213869) B2213869
theorem B1967883 : Blo 1967435 1967883 := bstep (se 1 (by rfl) ⟨1475912, by rfl⟩ : syracuseStep 1967883 = 2951825) B2951825
theorem B6641621 : Blo 1967435 6641621 := bbase (se 7 (by rfl) ⟨77831, by rfl⟩ : syracuseStep 6641621 = 155663) (by norm_num)
theorem B4427747 : Blo 1967435 4427747 := bstep (se 1 (by rfl) ⟨3320810, by rfl⟩ : syracuseStep 4427747 = 6641621) B6641621
theorem B2951831 : Blo 1967435 2951831 := bstep (se 1 (by rfl) ⟨2213873, by rfl⟩ : syracuseStep 2951831 = 4427747) B4427747
theorem B1967887 : Blo 1967435 1967887 := bstep (se 1 (by rfl) ⟨1475915, by rfl⟩ : syracuseStep 1967887 = 2951831) B2951831
theorem B2951837 : Blo 1967435 2951837 := bbase (se 3 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 2951837 = 1106939) (by norm_num)
theorem B1967891 : Blo 1967435 1967891 := bstep (se 1 (by rfl) ⟨1475918, by rfl⟩ : syracuseStep 1967891 = 2951837) B2951837
theorem B4427765 : Blo 1967435 4427765 := bbase (se 5 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 4427765 = 415103) (by norm_num)
theorem B2951843 : Blo 1967435 2951843 := bstep (se 1 (by rfl) ⟨2213882, by rfl⟩ : syracuseStep 2951843 = 4427765) B4427765
theorem B1967895 : Blo 1967435 1967895 := bstep (se 1 (by rfl) ⟨1475921, by rfl⟩ : syracuseStep 1967895 = 2951843) B2951843
theorem B2021965 : Blo 1967435 2021965 := bbase (se 3 (by rfl) ⟨379118, by rfl⟩ : syracuseStep 2021965 = 758237) (by norm_num)
theorem B10783813 : Blo 1967435 10783813 := bstep (se 4 (by rfl) ⟨1010982, by rfl⟩ : syracuseStep 10783813 = 2021965) B2021965
theorem B14378417 : Blo 1967435 14378417 := bstep (se 2 (by rfl) ⟨5391906, by rfl⟩ : syracuseStep 14378417 = 10783813) B10783813
theorem B9585611 : Blo 1967435 9585611 := bstep (se 1 (by rfl) ⟨7189208, by rfl⟩ : syracuseStep 9585611 = 14378417) B14378417
theorem B6390407 : Blo 1967435 6390407 := bstep (se 1 (by rfl) ⟨4792805, by rfl⟩ : syracuseStep 6390407 = 9585611) B9585611
theorem B4260271 : Blo 1967435 4260271 := bstep (se 1 (by rfl) ⟨3195203, by rfl⟩ : syracuseStep 4260271 = 6390407) B6390407
theorem B5680361 : Blo 1967435 5680361 := bstep (se 2 (by rfl) ⟨2130135, by rfl⟩ : syracuseStep 5680361 = 4260271) B4260271
theorem B3786907 : Blo 1967435 3786907 := bstep (se 1 (by rfl) ⟨2840180, by rfl⟩ : syracuseStep 3786907 = 5680361) B5680361
theorem B5049209 : Blo 1967435 5049209 := bstep (se 2 (by rfl) ⟨1893453, by rfl⟩ : syracuseStep 5049209 = 3786907) B3786907
theorem B3366139 : Blo 1967435 3366139 := bstep (se 1 (by rfl) ⟨2524604, by rfl⟩ : syracuseStep 3366139 = 5049209) B5049209
theorem B71810965 : Blo 1967435 71810965 := bstep (se 6 (by rfl) ⟨1683069, by rfl⟩ : syracuseStep 71810965 = 3366139) B3366139
theorem B95747953 : Blo 1967435 95747953 := bstep (se 2 (by rfl) ⟨35905482, by rfl⟩ : syracuseStep 95747953 = 71810965) B71810965
theorem B127663937 : Blo 1967435 127663937 := bstep (se 2 (by rfl) ⟨47873976, by rfl⟩ : syracuseStep 127663937 = 95747953) B95747953
theorem B85109291 : Blo 1967435 85109291 := bstep (se 1 (by rfl) ⟨63831968, by rfl⟩ : syracuseStep 85109291 = 127663937) B127663937
theorem B56739527 : Blo 1967435 56739527 := bstep (se 1 (by rfl) ⟨42554645, by rfl⟩ : syracuseStep 56739527 = 85109291) B85109291
theorem B37826351 : Blo 1967435 37826351 := bstep (se 1 (by rfl) ⟨28369763, by rfl⟩ : syracuseStep 37826351 = 56739527) B56739527
theorem B25217567 : Blo 1967435 25217567 := bstep (se 1 (by rfl) ⟨18913175, by rfl⟩ : syracuseStep 25217567 = 37826351) B37826351
theorem B16811711 : Blo 1967435 16811711 := bstep (se 1 (by rfl) ⟨12608783, by rfl⟩ : syracuseStep 16811711 = 25217567) B25217567
theorem B11207807 : Blo 1967435 11207807 := bstep (se 1 (by rfl) ⟨8405855, by rfl⟩ : syracuseStep 11207807 = 16811711) B16811711
theorem B7471871 : Blo 1967435 7471871 := bstep (se 1 (by rfl) ⟨5603903, by rfl⟩ : syracuseStep 7471871 = 11207807) B11207807
theorem B4981247 : Blo 1967435 4981247 := bstep (se 1 (by rfl) ⟨3735935, by rfl⟩ : syracuseStep 4981247 = 7471871) B7471871
theorem B3320831 : Blo 1967435 3320831 := bstep (se 1 (by rfl) ⟨2490623, by rfl⟩ : syracuseStep 3320831 = 4981247) B4981247
theorem B2213887 : Blo 1967435 2213887 := bstep (se 1 (by rfl) ⟨1660415, by rfl⟩ : syracuseStep 2213887 = 3320831) B3320831
theorem B2951849 : Blo 1967435 2951849 := bstep (se 2 (by rfl) ⟨1106943, by rfl⟩ : syracuseStep 2951849 = 2213887) B2213887
theorem B1967899 : Blo 1967435 1967899 := bstep (se 1 (by rfl) ⟨1475924, by rfl⟩ : syracuseStep 1967899 = 2951849) B2951849
theorem B2801957 : Blo 1967435 2801957 := bbase (se 4 (by rfl) ⟨262683, by rfl⟩ : syracuseStep 2801957 = 525367) (by norm_num)
theorem B7471885 : Blo 1967435 7471885 := bstep (se 3 (by rfl) ⟨1400978, by rfl⟩ : syracuseStep 7471885 = 2801957) B2801957
theorem B9962513 : Blo 1967435 9962513 := bstep (se 2 (by rfl) ⟨3735942, by rfl⟩ : syracuseStep 9962513 = 7471885) B7471885
theorem B6641675 : Blo 1967435 6641675 := bstep (se 1 (by rfl) ⟨4981256, by rfl⟩ : syracuseStep 6641675 = 9962513) B9962513
theorem B4427783 : Blo 1967435 4427783 := bstep (se 1 (by rfl) ⟨3320837, by rfl⟩ : syracuseStep 4427783 = 6641675) B6641675
theorem B2951855 : Blo 1967435 2951855 := bstep (se 1 (by rfl) ⟨2213891, by rfl⟩ : syracuseStep 2951855 = 4427783) B4427783
theorem B1967903 : Blo 1967435 1967903 := bstep (se 1 (by rfl) ⟨1475927, by rfl⟩ : syracuseStep 1967903 = 2951855) B2951855
theorem B2951861 : Blo 1967435 2951861 := bbase (se 5 (by rfl) ⟨138368, by rfl⟩ : syracuseStep 2951861 = 276737) (by norm_num)
theorem B1967907 : Blo 1967435 1967907 := bstep (se 1 (by rfl) ⟨1475930, by rfl⟩ : syracuseStep 1967907 = 2951861) B2951861
theorem B4981277 : Blo 1967435 4981277 := bbase (se 3 (by rfl) ⟨933989, by rfl⟩ : syracuseStep 4981277 = 1867979) (by norm_num)
theorem B3320851 : Blo 1967435 3320851 := bstep (se 1 (by rfl) ⟨2490638, by rfl⟩ : syracuseStep 3320851 = 4981277) B4981277
theorem B4427801 : Blo 1967435 4427801 := bstep (se 2 (by rfl) ⟨1660425, by rfl⟩ : syracuseStep 4427801 = 3320851) B3320851
theorem B2951867 : Blo 1967435 2951867 := bstep (se 1 (by rfl) ⟨2213900, by rfl⟩ : syracuseStep 2951867 = 4427801) B4427801
theorem B1967911 : Blo 1967435 1967911 := bstep (se 1 (by rfl) ⟨1475933, by rfl⟩ : syracuseStep 1967911 = 2951867) B2951867
theorem B2213905 : Blo 1967435 2213905 := bbase (se 2 (by rfl) ⟨830214, by rfl⟩ : syracuseStep 2213905 = 1660429) (by norm_num)
theorem B2951873 : Blo 1967435 2951873 := bstep (se 2 (by rfl) ⟨1106952, by rfl⟩ : syracuseStep 2951873 = 2213905) B2213905
theorem B1967915 : Blo 1967435 1967915 := bstep (se 1 (by rfl) ⟨1475936, by rfl⟩ : syracuseStep 1967915 = 2951873) B2951873
theorem B3735973 : Blo 1967435 3735973 := bbase (se 4 (by rfl) ⟨350247, by rfl⟩ : syracuseStep 3735973 = 700495) (by norm_num)
theorem B4981297 : Blo 1967435 4981297 := bstep (se 2 (by rfl) ⟨1867986, by rfl⟩ : syracuseStep 4981297 = 3735973) B3735973
theorem B6641729 : Blo 1967435 6641729 := bstep (se 2 (by rfl) ⟨2490648, by rfl⟩ : syracuseStep 6641729 = 4981297) B4981297
theorem B4427819 : Blo 1967435 4427819 := bstep (se 1 (by rfl) ⟨3320864, by rfl⟩ : syracuseStep 4427819 = 6641729) B6641729
theorem B2951879 : Blo 1967435 2951879 := bstep (se 1 (by rfl) ⟨2213909, by rfl⟩ : syracuseStep 2951879 = 4427819) B4427819
theorem B1967919 : Blo 1967435 1967919 := bstep (se 1 (by rfl) ⟨1475939, by rfl⟩ : syracuseStep 1967919 = 2951879) B2951879
theorem B2951885 : Blo 1967435 2951885 := bbase (se 3 (by rfl) ⟨553478, by rfl⟩ : syracuseStep 2951885 = 1106957) (by norm_num)
theorem B1967923 : Blo 1967435 1967923 := bstep (se 1 (by rfl) ⟨1475942, by rfl⟩ : syracuseStep 1967923 = 2951885) B2951885
theorem B4427837 : Blo 1967435 4427837 := bbase (se 3 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 4427837 = 1660439) (by norm_num)
theorem B2951891 : Blo 1967435 2951891 := bstep (se 1 (by rfl) ⟨2213918, by rfl⟩ : syracuseStep 2951891 = 4427837) B4427837
theorem B1967927 : Blo 1967435 1967927 := bstep (se 1 (by rfl) ⟨1475945, by rfl⟩ : syracuseStep 1967927 = 2951891) B2951891
theorem B3320885 : Blo 1967435 3320885 := bbase (se 5 (by rfl) ⟨155666, by rfl⟩ : syracuseStep 3320885 = 311333) (by norm_num)
theorem B2213923 : Blo 1967435 2213923 := bstep (se 1 (by rfl) ⟨1660442, by rfl⟩ : syracuseStep 2213923 = 3320885) B3320885
theorem B2951897 : Blo 1967435 2951897 := bstep (se 2 (by rfl) ⟨1106961, by rfl⟩ : syracuseStep 2951897 = 2213923) B2213923
theorem B1967931 : Blo 1967435 1967931 := bstep (se 1 (by rfl) ⟨1475948, by rfl⟩ : syracuseStep 1967931 = 2951897) B2951897
theorem B5604005 : Blo 1967435 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B14944013 : Blo 1967435 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B9962675 : Blo 1967435 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B6641783 : Blo 1967435 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B4427855 : Blo 1967435 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B2951903 : Blo 1967435 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B1967935 : Blo 1967435 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B2951909 : Blo 1967435 2951909 := bbase (se 4 (by rfl) ⟨276741, by rfl⟩ : syracuseStep 2951909 = 553483) (by norm_num)
theorem B1967939 : Blo 1967435 1967939 := bstep (se 1 (by rfl) ⟨1475954, by rfl⟩ : syracuseStep 1967939 = 2951909) B2951909
theorem B3546301 : Blo 1967435 3546301 := bbase (se 3 (by rfl) ⟨664931, by rfl⟩ : syracuseStep 3546301 = 1329863) (by norm_num)
theorem B4728401 : Blo 1967435 4728401 := bstep (se 2 (by rfl) ⟨1773150, by rfl⟩ : syracuseStep 4728401 = 3546301) B3546301
theorem B3152267 : Blo 1967435 3152267 := bstep (se 1 (by rfl) ⟨2364200, by rfl⟩ : syracuseStep 3152267 = 4728401) B4728401
theorem B2101511 : Blo 1967435 2101511 := bstep (se 1 (by rfl) ⟨1576133, by rfl⟩ : syracuseStep 2101511 = 3152267) B3152267
theorem B5604029 : Blo 1967435 5604029 := bstep (se 3 (by rfl) ⟨1050755, by rfl⟩ : syracuseStep 5604029 = 2101511) B2101511
theorem B3736019 : Blo 1967435 3736019 := bstep (se 1 (by rfl) ⟨2802014, by rfl⟩ : syracuseStep 3736019 = 5604029) B5604029
theorem B2490679 : Blo 1967435 2490679 := bstep (se 1 (by rfl) ⟨1868009, by rfl⟩ : syracuseStep 2490679 = 3736019) B3736019
theorem B3320905 : Blo 1967435 3320905 := bstep (se 2 (by rfl) ⟨1245339, by rfl⟩ : syracuseStep 3320905 = 2490679) B2490679
theorem B4427873 : Blo 1967435 4427873 := bstep (se 2 (by rfl) ⟨1660452, by rfl⟩ : syracuseStep 4427873 = 3320905) B3320905
theorem B2951915 : Blo 1967435 2951915 := bstep (se 1 (by rfl) ⟨2213936, by rfl⟩ : syracuseStep 2951915 = 4427873) B4427873
theorem B1967943 : Blo 1967435 1967943 := bstep (se 1 (by rfl) ⟨1475957, by rfl⟩ : syracuseStep 1967943 = 2951915) B2951915
theorem B2213941 : Blo 1967435 2213941 := bbase (se 5 (by rfl) ⟨103778, by rfl⟩ : syracuseStep 2213941 = 207557) (by norm_num)
theorem B2951921 : Blo 1967435 2951921 := bstep (se 2 (by rfl) ⟨1106970, by rfl⟩ : syracuseStep 2951921 = 2213941) B2213941
theorem B1967947 : Blo 1967435 1967947 := bstep (se 1 (by rfl) ⟨1475960, by rfl⟩ : syracuseStep 1967947 = 2951921) B2951921
theorem B2490689 : Blo 1967435 2490689 := bbase (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) (by norm_num)
theorem B6641837 : Blo 1967435 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B4427891 : Blo 1967435 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B2951927 : Blo 1967435 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B1967951 : Blo 1967435 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B2951933 : Blo 1967435 2951933 := bbase (se 3 (by rfl) ⟨553487, by rfl⟩ : syracuseStep 2951933 = 1106975) (by norm_num)
theorem B1967955 : Blo 1967435 1967955 := bstep (se 1 (by rfl) ⟨1475966, by rfl⟩ : syracuseStep 1967955 = 2951933) B2951933
theorem B4427909 : Blo 1967435 4427909 := bbase (se 4 (by rfl) ⟨415116, by rfl⟩ : syracuseStep 4427909 = 830233) (by norm_num)
theorem B2951939 : Blo 1967435 2951939 := bstep (se 1 (by rfl) ⟨2213954, by rfl⟩ : syracuseStep 2951939 = 4427909) B4427909
theorem B1967959 : Blo 1967435 1967959 := bstep (se 1 (by rfl) ⟨1475969, by rfl⟩ : syracuseStep 1967959 = 2951939) B2951939
theorem B4260413 : Blo 1967435 4260413 := bbase (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) (by norm_num)
theorem B2840275 : Blo 1967435 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B15148133 : Blo 1967435 15148133 := bstep (se 4 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 15148133 = 2840275) B2840275
theorem B10098755 : Blo 1967435 10098755 := bstep (se 1 (by rfl) ⟨7574066, by rfl⟩ : syracuseStep 10098755 = 15148133) B15148133
theorem B6732503 : Blo 1967435 6732503 := bstep (se 1 (by rfl) ⟨5049377, by rfl⟩ : syracuseStep 6732503 = 10098755) B10098755
theorem B4488335 : Blo 1967435 4488335 := bstep (se 1 (by rfl) ⟨3366251, by rfl⟩ : syracuseStep 4488335 = 6732503) B6732503
theorem B2992223 : Blo 1967435 2992223 := bstep (se 1 (by rfl) ⟨2244167, by rfl⟩ : syracuseStep 2992223 = 4488335) B4488335
theorem B1994815 : Blo 1967435 1994815 := bstep (se 1 (by rfl) ⟨1496111, by rfl⟩ : syracuseStep 1994815 = 2992223) B2992223
theorem B2659753 : Blo 1967435 2659753 := bstep (se 2 (by rfl) ⟨997407, by rfl⟩ : syracuseStep 2659753 = 1994815) B1994815
theorem B3546337 : Blo 1967435 3546337 := bstep (se 2 (by rfl) ⟨1329876, by rfl⟩ : syracuseStep 3546337 = 2659753) B2659753
theorem B4728449 : Blo 1967435 4728449 := bstep (se 2 (by rfl) ⟨1773168, by rfl⟩ : syracuseStep 4728449 = 3546337) B3546337
theorem B3152299 : Blo 1967435 3152299 := bstep (se 1 (by rfl) ⟨2364224, by rfl⟩ : syracuseStep 3152299 = 4728449) B4728449
theorem B4203065 : Blo 1967435 4203065 := bstep (se 2 (by rfl) ⟨1576149, by rfl⟩ : syracuseStep 4203065 = 3152299) B3152299
theorem B2802043 : Blo 1967435 2802043 := bstep (se 1 (by rfl) ⟨2101532, by rfl⟩ : syracuseStep 2802043 = 4203065) B4203065
theorem B3736057 : Blo 1967435 3736057 := bstep (se 2 (by rfl) ⟨1401021, by rfl⟩ : syracuseStep 3736057 = 2802043) B2802043
theorem B4981409 : Blo 1967435 4981409 := bstep (se 2 (by rfl) ⟨1868028, by rfl⟩ : syracuseStep 4981409 = 3736057) B3736057
theorem B3320939 : Blo 1967435 3320939 := bstep (se 1 (by rfl) ⟨2490704, by rfl⟩ : syracuseStep 3320939 = 4981409) B4981409
theorem B2213959 : Blo 1967435 2213959 := bstep (se 1 (by rfl) ⟨1660469, by rfl⟩ : syracuseStep 2213959 = 3320939) B3320939
theorem B2951945 : Blo 1967435 2951945 := bstep (se 2 (by rfl) ⟨1106979, by rfl⟩ : syracuseStep 2951945 = 2213959) B2213959
theorem B1967963 : Blo 1967435 1967963 := bstep (se 1 (by rfl) ⟨1475972, by rfl⟩ : syracuseStep 1967963 = 2951945) B2951945
theorem B9962837 : Blo 1967435 9962837 := bbase (se 12 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 9962837 = 7297) (by norm_num)
theorem B6641891 : Blo 1967435 6641891 := bstep (se 1 (by rfl) ⟨4981418, by rfl⟩ : syracuseStep 6641891 = 9962837) B9962837
theorem B4427927 : Blo 1967435 4427927 := bstep (se 1 (by rfl) ⟨3320945, by rfl⟩ : syracuseStep 4427927 = 6641891) B6641891
theorem B2951951 : Blo 1967435 2951951 := bstep (se 1 (by rfl) ⟨2213963, by rfl⟩ : syracuseStep 2951951 = 4427927) B4427927
theorem B1967967 : Blo 1967435 1967967 := bstep (se 1 (by rfl) ⟨1475975, by rfl⟩ : syracuseStep 1967967 = 2951951) B2951951
theorem B2951957 : Blo 1967435 2951957 := bbase (se 6 (by rfl) ⟨69186, by rfl⟩ : syracuseStep 2951957 = 138373) (by norm_num)
theorem B1967971 : Blo 1967435 1967971 := bstep (se 1 (by rfl) ⟨1475978, by rfl⟩ : syracuseStep 1967971 = 2951957) B2951957
theorem B14378965 : Blo 1967435 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B76687813 : Blo 1967435 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B409001669 : Blo 1967435 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B272667779 : Blo 1967435 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B181778519 : Blo 1967435 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B121185679 : Blo 1967435 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B161580905 : Blo 1967435 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B107720603 : Blo 1967435 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B71813735 : Blo 1967435 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B47875823 : Blo 1967435 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B31917215 : Blo 1967435 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B21278143 : Blo 1967435 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B28370857 : Blo 1967435 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B37827809 : Blo 1967435 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B25218539 : Blo 1967435 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B16812359 : Blo 1967435 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B11208239 : Blo 1967435 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B7472159 : Blo 1967435 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B4981439 : Blo 1967435 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B3320959 : Blo 1967435 3320959 := bstep (se 1 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 3320959 = 4981439) B4981439
theorem B4427945 : Blo 1967435 4427945 := bstep (se 2 (by rfl) ⟨1660479, by rfl⟩ : syracuseStep 4427945 = 3320959) B3320959
theorem B2951963 : Blo 1967435 2951963 := bstep (se 1 (by rfl) ⟨2213972, by rfl⟩ : syracuseStep 2951963 = 4427945) B4427945
theorem B1967975 : Blo 1967435 1967975 := bstep (se 1 (by rfl) ⟨1475981, by rfl⟩ : syracuseStep 1967975 = 2951963) B2951963
theorem B2213977 : Blo 1967435 2213977 := bbase (se 2 (by rfl) ⟨830241, by rfl⟩ : syracuseStep 2213977 = 1660483) (by norm_num)
theorem B2951969 : Blo 1967435 2951969 := bstep (se 2 (by rfl) ⟨1106988, by rfl⟩ : syracuseStep 2951969 = 2213977) B2213977
theorem B1967979 : Blo 1967435 1967979 := bstep (se 1 (by rfl) ⟨1475984, by rfl⟩ : syracuseStep 1967979 = 2951969) B2951969
theorem B6304661 : Blo 1967435 6304661 := bbase (se 6 (by rfl) ⟨147765, by rfl⟩ : syracuseStep 6304661 = 295531) (by norm_num)
theorem B4203107 : Blo 1967435 4203107 := bstep (se 1 (by rfl) ⟨3152330, by rfl⟩ : syracuseStep 4203107 = 6304661) B6304661
theorem B2802071 : Blo 1967435 2802071 := bstep (se 1 (by rfl) ⟨2101553, by rfl⟩ : syracuseStep 2802071 = 4203107) B4203107
theorem B7472189 : Blo 1967435 7472189 := bstep (se 3 (by rfl) ⟨1401035, by rfl⟩ : syracuseStep 7472189 = 2802071) B2802071
theorem B4981459 : Blo 1967435 4981459 := bstep (se 1 (by rfl) ⟨3736094, by rfl⟩ : syracuseStep 4981459 = 7472189) B7472189
theorem B6641945 : Blo 1967435 6641945 := bstep (se 2 (by rfl) ⟨2490729, by rfl⟩ : syracuseStep 6641945 = 4981459) B4981459
theorem B4427963 : Blo 1967435 4427963 := bstep (se 1 (by rfl) ⟨3320972, by rfl⟩ : syracuseStep 4427963 = 6641945) B6641945
theorem B2951975 : Blo 1967435 2951975 := bstep (se 1 (by rfl) ⟨2213981, by rfl⟩ : syracuseStep 2951975 = 4427963) B4427963
theorem B1967983 : Blo 1967435 1967983 := bstep (se 1 (by rfl) ⟨1475987, by rfl⟩ : syracuseStep 1967983 = 2951975) B2951975
theorem B2951981 : Blo 1967435 2951981 := bbase (se 3 (by rfl) ⟨553496, by rfl⟩ : syracuseStep 2951981 = 1106993) (by norm_num)
theorem B1967987 : Blo 1967435 1967987 := bstep (se 1 (by rfl) ⟨1475990, by rfl⟩ : syracuseStep 1967987 = 2951981) B2951981
theorem B4427981 : Blo 1967435 4427981 := bbase (se 3 (by rfl) ⟨830246, by rfl⟩ : syracuseStep 4427981 = 1660493) (by norm_num)
theorem B2951987 : Blo 1967435 2951987 := bstep (se 1 (by rfl) ⟨2213990, by rfl⟩ : syracuseStep 2951987 = 4427981) B4427981
theorem B1967991 : Blo 1967435 1967991 := bstep (se 1 (by rfl) ⟨1475993, by rfl⟩ : syracuseStep 1967991 = 2951987) B2951987
theorem B2490745 : Blo 1967435 2490745 := bbase (se 2 (by rfl) ⟨934029, by rfl⟩ : syracuseStep 2490745 = 1868059) (by norm_num)
theorem B3320993 : Blo 1967435 3320993 := bstep (se 2 (by rfl) ⟨1245372, by rfl⟩ : syracuseStep 3320993 = 2490745) B2490745
theorem B2213995 : Blo 1967435 2213995 := bstep (se 1 (by rfl) ⟨1660496, by rfl⟩ : syracuseStep 2213995 = 3320993) B3320993
theorem B2951993 : Blo 1967435 2951993 := bstep (se 2 (by rfl) ⟨1106997, by rfl⟩ : syracuseStep 2951993 = 2213995) B2213995
theorem B1967995 : Blo 1967435 1967995 := bstep (se 1 (by rfl) ⟨1475996, by rfl⟩ : syracuseStep 1967995 = 2951993) B2951993
theorem B7189573 : Blo 1967435 7189573 := bbase (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) (by norm_num)
theorem B9586097 : Blo 1967435 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B6390731 : Blo 1967435 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B4260487 : Blo 1967435 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B5680649 : Blo 1967435 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B15148397 : Blo 1967435 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B10098931 : Blo 1967435 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B13465241 : Blo 1967435 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B8976827 : Blo 1967435 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B5984551 : Blo 1967435 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B7979401 : Blo 1967435 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B10639201 : Blo 1967435 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B14185601 : Blo 1967435 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B9457067 : Blo 1967435 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B6304711 : Blo 1967435 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B8406281 : Blo 1967435 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B22416749 : Blo 1967435 22416749 := bstep (se 3 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 22416749 = 8406281) B8406281
theorem B14944499 : Blo 1967435 14944499 := bstep (se 1 (by rfl) ⟨11208374, by rfl⟩ : syracuseStep 14944499 = 22416749) B22416749
theorem B9962999 : Blo 1967435 9962999 := bstep (se 1 (by rfl) ⟨7472249, by rfl⟩ : syracuseStep 9962999 = 14944499) B14944499
theorem B6641999 : Blo 1967435 6641999 := bstep (se 1 (by rfl) ⟨4981499, by rfl⟩ : syracuseStep 6641999 = 9962999) B9962999
theorem B4427999 : Blo 1967435 4427999 := bstep (se 1 (by rfl) ⟨3320999, by rfl⟩ : syracuseStep 4427999 = 6641999) B6641999
theorem B2951999 : Blo 1967435 2951999 := bstep (se 1 (by rfl) ⟨2213999, by rfl⟩ : syracuseStep 2951999 = 4427999) B4427999
theorem B1967999 : Blo 1967435 1967999 := bstep (se 1 (by rfl) ⟨1475999, by rfl⟩ : syracuseStep 1967999 = 2951999) B2951999
theorem B2952005 : Blo 1967435 2952005 := bbase (se 4 (by rfl) ⟨276750, by rfl⟩ : syracuseStep 2952005 = 553501) (by norm_num)
theorem B1968003 : Blo 1967435 1968003 := bstep (se 1 (by rfl) ⟨1476002, by rfl⟩ : syracuseStep 1968003 = 2952005) B2952005
theorem B3321013 : Blo 1967435 3321013 := bbase (se 5 (by rfl) ⟨155672, by rfl⟩ : syracuseStep 3321013 = 311345) (by norm_num)
theorem B4428017 : Blo 1967435 4428017 := bstep (se 2 (by rfl) ⟨1660506, by rfl⟩ : syracuseStep 4428017 = 3321013) B3321013
theorem B2952011 : Blo 1967435 2952011 := bstep (se 1 (by rfl) ⟨2214008, by rfl⟩ : syracuseStep 2952011 = 4428017) B4428017
theorem B1968007 : Blo 1967435 1968007 := bstep (se 1 (by rfl) ⟨1476005, by rfl⟩ : syracuseStep 1968007 = 2952011) B2952011
theorem B2214013 : Blo 1967435 2214013 := bbase (se 3 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 2214013 = 830255) (by norm_num)
theorem B2952017 : Blo 1967435 2952017 := bstep (se 2 (by rfl) ⟨1107006, by rfl⟩ : syracuseStep 2952017 = 2214013) B2214013
theorem B1968011 : Blo 1967435 1968011 := bstep (se 1 (by rfl) ⟨1476008, by rfl⟩ : syracuseStep 1968011 = 2952017) B2952017
theorem B6642053 : Blo 1967435 6642053 := bbase (se 4 (by rfl) ⟨622692, by rfl⟩ : syracuseStep 6642053 = 1245385) (by norm_num)
theorem B4428035 : Blo 1967435 4428035 := bstep (se 1 (by rfl) ⟨3321026, by rfl⟩ : syracuseStep 4428035 = 6642053) B6642053
theorem B2952023 : Blo 1967435 2952023 := bstep (se 1 (by rfl) ⟨2214017, by rfl⟩ : syracuseStep 2952023 = 4428035) B4428035
theorem B1968015 : Blo 1967435 1968015 := bstep (se 1 (by rfl) ⟨1476011, by rfl⟩ : syracuseStep 1968015 = 2952023) B2952023
theorem B2952029 : Blo 1967435 2952029 := bbase (se 3 (by rfl) ⟨553505, by rfl⟩ : syracuseStep 2952029 = 1107011) (by norm_num)
theorem B1968019 : Blo 1967435 1968019 := bstep (se 1 (by rfl) ⟨1476014, by rfl⟩ : syracuseStep 1968019 = 2952029) B2952029
theorem B4428053 : Blo 1967435 4428053 := bbase (se 6 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 4428053 = 207565) (by norm_num)
theorem B2952035 : Blo 1967435 2952035 := bstep (se 1 (by rfl) ⟨2214026, by rfl⟩ : syracuseStep 2952035 = 4428053) B4428053
theorem B1968023 : Blo 1967435 1968023 := bstep (se 1 (by rfl) ⟨1476017, by rfl⟩ : syracuseStep 1968023 = 2952035) B2952035
theorem B7472357 : Blo 1967435 7472357 := bbase (se 4 (by rfl) ⟨700533, by rfl⟩ : syracuseStep 7472357 = 1401067) (by norm_num)
theorem B4981571 : Blo 1967435 4981571 := bstep (se 1 (by rfl) ⟨3736178, by rfl⟩ : syracuseStep 4981571 = 7472357) B7472357
theorem B3321047 : Blo 1967435 3321047 := bstep (se 1 (by rfl) ⟨2490785, by rfl⟩ : syracuseStep 3321047 = 4981571) B4981571
theorem B2214031 : Blo 1967435 2214031 := bstep (se 1 (by rfl) ⟨1660523, by rfl⟩ : syracuseStep 2214031 = 3321047) B3321047
theorem B2952041 : Blo 1967435 2952041 := bstep (se 2 (by rfl) ⟨1107015, by rfl⟩ : syracuseStep 2952041 = 2214031) B2214031
theorem B1968027 : Blo 1967435 1968027 := bstep (se 1 (by rfl) ⟨1476020, by rfl⟩ : syracuseStep 1968027 = 2952041) B2952041
theorem B7092917 : Blo 1967435 7092917 := bbase (se 5 (by rfl) ⟨332480, by rfl⟩ : syracuseStep 7092917 = 664961) (by norm_num)
theorem B4728611 : Blo 1967435 4728611 := bstep (se 1 (by rfl) ⟨3546458, by rfl⟩ : syracuseStep 4728611 = 7092917) B7092917
theorem B3152407 : Blo 1967435 3152407 := bstep (se 1 (by rfl) ⟨2364305, by rfl⟩ : syracuseStep 3152407 = 4728611) B4728611
theorem B4203209 : Blo 1967435 4203209 := bstep (se 2 (by rfl) ⟨1576203, by rfl⟩ : syracuseStep 4203209 = 3152407) B3152407
theorem B11208557 : Blo 1967435 11208557 := bstep (se 3 (by rfl) ⟨2101604, by rfl⟩ : syracuseStep 11208557 = 4203209) B4203209
theorem B7472371 : Blo 1967435 7472371 := bstep (se 1 (by rfl) ⟨5604278, by rfl⟩ : syracuseStep 7472371 = 11208557) B11208557
theorem B9963161 : Blo 1967435 9963161 := bstep (se 2 (by rfl) ⟨3736185, by rfl⟩ : syracuseStep 9963161 = 7472371) B7472371
theorem B6642107 : Blo 1967435 6642107 := bstep (se 1 (by rfl) ⟨4981580, by rfl⟩ : syracuseStep 6642107 = 9963161) B9963161
theorem B4428071 : Blo 1967435 4428071 := bstep (se 1 (by rfl) ⟨3321053, by rfl⟩ : syracuseStep 4428071 = 6642107) B6642107
theorem B2952047 : Blo 1967435 2952047 := bstep (se 1 (by rfl) ⟨2214035, by rfl⟩ : syracuseStep 2952047 = 4428071) B4428071
theorem B1968031 : Blo 1967435 1968031 := bstep (se 1 (by rfl) ⟨1476023, by rfl⟩ : syracuseStep 1968031 = 2952047) B2952047
theorem B2952053 : Blo 1967435 2952053 := bbase (se 5 (by rfl) ⟨138377, by rfl⟩ : syracuseStep 2952053 = 276755) (by norm_num)
theorem B1968035 : Blo 1967435 1968035 := bstep (se 1 (by rfl) ⟨1476026, by rfl⟩ : syracuseStep 1968035 = 2952053) B2952053
theorem B8977013 : Blo 1967435 8977013 := bbase (se 5 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 8977013 = 841595) (by norm_num)
theorem B5984675 : Blo 1967435 5984675 := bstep (se 1 (by rfl) ⟨4488506, by rfl⟩ : syracuseStep 5984675 = 8977013) B8977013
theorem B3989783 : Blo 1967435 3989783 := bstep (se 1 (by rfl) ⟨2992337, by rfl⟩ : syracuseStep 3989783 = 5984675) B5984675
theorem B10639421 : Blo 1967435 10639421 := bstep (se 3 (by rfl) ⟨1994891, by rfl⟩ : syracuseStep 10639421 = 3989783) B3989783
theorem B7092947 : Blo 1967435 7092947 := bstep (se 1 (by rfl) ⟨5319710, by rfl⟩ : syracuseStep 7092947 = 10639421) B10639421
theorem B4728631 : Blo 1967435 4728631 := bstep (se 1 (by rfl) ⟨3546473, by rfl⟩ : syracuseStep 4728631 = 7092947) B7092947
theorem B6304841 : Blo 1967435 6304841 := bstep (se 2 (by rfl) ⟨2364315, by rfl⟩ : syracuseStep 6304841 = 4728631) B4728631
theorem B4203227 : Blo 1967435 4203227 := bstep (se 1 (by rfl) ⟨3152420, by rfl⟩ : syracuseStep 4203227 = 6304841) B6304841
theorem B2802151 : Blo 1967435 2802151 := bstep (se 1 (by rfl) ⟨2101613, by rfl⟩ : syracuseStep 2802151 = 4203227) B4203227
theorem B3736201 : Blo 1967435 3736201 := bstep (se 2 (by rfl) ⟨1401075, by rfl⟩ : syracuseStep 3736201 = 2802151) B2802151
theorem B4981601 : Blo 1967435 4981601 := bstep (se 2 (by rfl) ⟨1868100, by rfl⟩ : syracuseStep 4981601 = 3736201) B3736201
theorem B3321067 : Blo 1967435 3321067 := bstep (se 1 (by rfl) ⟨2490800, by rfl⟩ : syracuseStep 3321067 = 4981601) B4981601
theorem B4428089 : Blo 1967435 4428089 := bstep (se 2 (by rfl) ⟨1660533, by rfl⟩ : syracuseStep 4428089 = 3321067) B3321067
theorem B2952059 : Blo 1967435 2952059 := bstep (se 1 (by rfl) ⟨2214044, by rfl⟩ : syracuseStep 2952059 = 4428089) B4428089
theorem B1968039 : Blo 1967435 1968039 := bstep (se 1 (by rfl) ⟨1476029, by rfl⟩ : syracuseStep 1968039 = 2952059) B2952059
theorem B2214049 : Blo 1967435 2214049 := bbase (se 2 (by rfl) ⟨830268, by rfl⟩ : syracuseStep 2214049 = 1660537) (by norm_num)
theorem B2952065 : Blo 1967435 2952065 := bstep (se 2 (by rfl) ⟨1107024, by rfl⟩ : syracuseStep 2952065 = 2214049) B2214049
theorem B1968043 : Blo 1967435 1968043 := bstep (se 1 (by rfl) ⟨1476032, by rfl⟩ : syracuseStep 1968043 = 2952065) B2952065
theorem B4981621 : Blo 1967435 4981621 := bbase (se 5 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 4981621 = 467027) (by norm_num)
theorem B6642161 : Blo 1967435 6642161 := bstep (se 2 (by rfl) ⟨2490810, by rfl⟩ : syracuseStep 6642161 = 4981621) B4981621
theorem B4428107 : Blo 1967435 4428107 := bstep (se 1 (by rfl) ⟨3321080, by rfl⟩ : syracuseStep 4428107 = 6642161) B6642161
theorem B2952071 : Blo 1967435 2952071 := bstep (se 1 (by rfl) ⟨2214053, by rfl⟩ : syracuseStep 2952071 = 4428107) B4428107
theorem B1968047 : Blo 1967435 1968047 := bstep (se 1 (by rfl) ⟨1476035, by rfl⟩ : syracuseStep 1968047 = 2952071) B2952071
theorem B2952077 : Blo 1967435 2952077 := bbase (se 3 (by rfl) ⟨553514, by rfl⟩ : syracuseStep 2952077 = 1107029) (by norm_num)
theorem B1968051 : Blo 1967435 1968051 := bstep (se 1 (by rfl) ⟨1476038, by rfl⟩ : syracuseStep 1968051 = 2952077) B2952077
theorem B4428125 : Blo 1967435 4428125 := bbase (se 3 (by rfl) ⟨830273, by rfl⟩ : syracuseStep 4428125 = 1660547) (by norm_num)
theorem B2952083 : Blo 1967435 2952083 := bstep (se 1 (by rfl) ⟨2214062, by rfl⟩ : syracuseStep 2952083 = 4428125) B4428125
theorem B1968055 : Blo 1967435 1968055 := bstep (se 1 (by rfl) ⟨1476041, by rfl⟩ : syracuseStep 1968055 = 2952083) B2952083
theorem B3321101 : Blo 1967435 3321101 := bbase (se 3 (by rfl) ⟨622706, by rfl⟩ : syracuseStep 3321101 = 1245413) (by norm_num)
theorem B2214067 : Blo 1967435 2214067 := bstep (se 1 (by rfl) ⟨1660550, by rfl⟩ : syracuseStep 2214067 = 3321101) B3321101
theorem B2952089 : Blo 1967435 2952089 := bstep (se 2 (by rfl) ⟨1107033, by rfl⟩ : syracuseStep 2952089 = 2214067) B2214067
theorem B1968059 : Blo 1967435 1968059 := bstep (se 1 (by rfl) ⟨1476044, by rfl⟩ : syracuseStep 1968059 = 2952089) B2952089
theorem B16813109 : Blo 1967435 16813109 := bbase (se 5 (by rfl) ⟨788114, by rfl⟩ : syracuseStep 16813109 = 1576229) (by norm_num)
theorem B11208739 : Blo 1967435 11208739 := bstep (se 1 (by rfl) ⟨8406554, by rfl⟩ : syracuseStep 11208739 = 16813109) B16813109
theorem B14944985 : Blo 1967435 14944985 := bstep (se 2 (by rfl) ⟨5604369, by rfl⟩ : syracuseStep 14944985 = 11208739) B11208739
theorem B9963323 : Blo 1967435 9963323 := bstep (se 1 (by rfl) ⟨7472492, by rfl⟩ : syracuseStep 9963323 = 14944985) B14944985
theorem B6642215 : Blo 1967435 6642215 := bstep (se 1 (by rfl) ⟨4981661, by rfl⟩ : syracuseStep 6642215 = 9963323) B9963323
theorem B4428143 : Blo 1967435 4428143 := bstep (se 1 (by rfl) ⟨3321107, by rfl⟩ : syracuseStep 4428143 = 6642215) B6642215
theorem B2952095 : Blo 1967435 2952095 := bstep (se 1 (by rfl) ⟨2214071, by rfl⟩ : syracuseStep 2952095 = 4428143) B4428143
theorem B1968063 : Blo 1967435 1968063 := bstep (se 1 (by rfl) ⟨1476047, by rfl⟩ : syracuseStep 1968063 = 2952095) B2952095
theorem B2952101 : Blo 1967435 2952101 := bbase (se 4 (by rfl) ⟨276759, by rfl⟩ : syracuseStep 2952101 = 553519) (by norm_num)
theorem B1968067 : Blo 1967435 1968067 := bstep (se 1 (by rfl) ⟨1476050, by rfl⟩ : syracuseStep 1968067 = 2952101) B2952101
theorem B2490841 : Blo 1967435 2490841 := bbase (se 2 (by rfl) ⟨934065, by rfl⟩ : syracuseStep 2490841 = 1868131) (by norm_num)
theorem B3321121 : Blo 1967435 3321121 := bstep (se 2 (by rfl) ⟨1245420, by rfl⟩ : syracuseStep 3321121 = 2490841) B2490841
theorem B4428161 : Blo 1967435 4428161 := bstep (se 2 (by rfl) ⟨1660560, by rfl⟩ : syracuseStep 4428161 = 3321121) B3321121
theorem B2952107 : Blo 1967435 2952107 := bstep (se 1 (by rfl) ⟨2214080, by rfl⟩ : syracuseStep 2952107 = 4428161) B4428161
theorem B1968071 : Blo 1967435 1968071 := bstep (se 1 (by rfl) ⟨1476053, by rfl⟩ : syracuseStep 1968071 = 2952107) B2952107
theorem B2214085 : Blo 1967435 2214085 := bbase (se 4 (by rfl) ⟨207570, by rfl⟩ : syracuseStep 2214085 = 415141) (by norm_num)
theorem B2952113 : Blo 1967435 2952113 := bstep (se 2 (by rfl) ⟨1107042, by rfl⟩ : syracuseStep 2952113 = 2214085) B2214085
theorem B1968075 : Blo 1967435 1968075 := bstep (se 1 (by rfl) ⟨1476056, by rfl⟩ : syracuseStep 1968075 = 2952113) B2952113
theorem B3736277 : Blo 1967435 3736277 := bbase (se 7 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 3736277 = 87569) (by norm_num)
theorem B2490851 : Blo 1967435 2490851 := bstep (se 1 (by rfl) ⟨1868138, by rfl⟩ : syracuseStep 2490851 = 3736277) B3736277
theorem B6642269 : Blo 1967435 6642269 := bstep (se 3 (by rfl) ⟨1245425, by rfl⟩ : syracuseStep 6642269 = 2490851) B2490851
theorem B4428179 : Blo 1967435 4428179 := bstep (se 1 (by rfl) ⟨3321134, by rfl⟩ : syracuseStep 4428179 = 6642269) B6642269
theorem B2952119 : Blo 1967435 2952119 := bstep (se 1 (by rfl) ⟨2214089, by rfl⟩ : syracuseStep 2952119 = 4428179) B4428179
theorem B1968079 : Blo 1967435 1968079 := bstep (se 1 (by rfl) ⟨1476059, by rfl⟩ : syracuseStep 1968079 = 2952119) B2952119
theorem B2952125 : Blo 1967435 2952125 := bbase (se 3 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 2952125 = 1107047) (by norm_num)
theorem B1968083 : Blo 1967435 1968083 := bstep (se 1 (by rfl) ⟨1476062, by rfl⟩ : syracuseStep 1968083 = 2952125) B2952125
theorem B4428197 : Blo 1967435 4428197 := bbase (se 4 (by rfl) ⟨415143, by rfl⟩ : syracuseStep 4428197 = 830287) (by norm_num)
theorem B2952131 : Blo 1967435 2952131 := bstep (se 1 (by rfl) ⟨2214098, by rfl⟩ : syracuseStep 2952131 = 4428197) B4428197
theorem B1968087 : Blo 1967435 1968087 := bstep (se 1 (by rfl) ⟨1476065, by rfl⟩ : syracuseStep 1968087 = 2952131) B2952131
theorem B4981733 : Blo 1967435 4981733 := bbase (se 4 (by rfl) ⟨467037, by rfl⟩ : syracuseStep 4981733 = 934075) (by norm_num)
theorem B3321155 : Blo 1967435 3321155 := bstep (se 1 (by rfl) ⟨2490866, by rfl⟩ : syracuseStep 3321155 = 4981733) B4981733
theorem B2214103 : Blo 1967435 2214103 := bstep (se 1 (by rfl) ⟨1660577, by rfl⟩ : syracuseStep 2214103 = 3321155) B3321155
theorem B2952137 : Blo 1967435 2952137 := bstep (se 2 (by rfl) ⟨1107051, by rfl⟩ : syracuseStep 2952137 = 2214103) B2214103
theorem B1968091 : Blo 1967435 1968091 := bstep (se 1 (by rfl) ⟨1476068, by rfl⟩ : syracuseStep 1968091 = 2952137) B2952137
theorem B2101673 : Blo 1967435 2101673 := bbase (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) (by norm_num)
theorem B5604461 : Blo 1967435 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B3736307 : Blo 1967435 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B9963485 : Blo 1967435 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B6642323 : Blo 1967435 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B4428215 : Blo 1967435 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B2952143 : Blo 1967435 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B1968095 : Blo 1967435 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B2952149 : Blo 1967435 2952149 := bbase (se 7 (by rfl) ⟨34595, by rfl⟩ : syracuseStep 2952149 = 69191) (by norm_num)
theorem B1968099 : Blo 1967435 1968099 := bstep (se 1 (by rfl) ⟨1476074, by rfl⟩ : syracuseStep 1968099 = 2952149) B2952149
theorem B7472645 : Blo 1967435 7472645 := bbase (se 4 (by rfl) ⟨700560, by rfl⟩ : syracuseStep 7472645 = 1401121) (by norm_num)
theorem B4981763 : Blo 1967435 4981763 := bstep (se 1 (by rfl) ⟨3736322, by rfl⟩ : syracuseStep 4981763 = 7472645) B7472645
theorem B3321175 : Blo 1967435 3321175 := bstep (se 1 (by rfl) ⟨2490881, by rfl⟩ : syracuseStep 3321175 = 4981763) B4981763
theorem B4428233 : Blo 1967435 4428233 := bstep (se 2 (by rfl) ⟨1660587, by rfl⟩ : syracuseStep 4428233 = 3321175) B3321175
theorem B2952155 : Blo 1967435 2952155 := bstep (se 1 (by rfl) ⟨2214116, by rfl⟩ : syracuseStep 2952155 = 4428233) B4428233
theorem B1968103 : Blo 1967435 1968103 := bstep (se 1 (by rfl) ⟨1476077, by rfl⟩ : syracuseStep 1968103 = 2952155) B2952155
theorem B2214121 : Blo 1967435 2214121 := bbase (se 2 (by rfl) ⟨830295, by rfl⟩ : syracuseStep 2214121 = 1660591) (by norm_num)
theorem B2952161 : Blo 1967435 2952161 := bstep (se 2 (by rfl) ⟨1107060, by rfl⟩ : syracuseStep 2952161 = 2214121) B2214121
theorem B1968107 : Blo 1967435 1968107 := bstep (se 1 (by rfl) ⟨1476080, by rfl⟩ : syracuseStep 1968107 = 2952161) B2952161
theorem B11209013 : Blo 1967435 11209013 := bbase (se 5 (by rfl) ⟨525422, by rfl⟩ : syracuseStep 11209013 = 1050845) (by norm_num)
theorem B7472675 : Blo 1967435 7472675 := bstep (se 1 (by rfl) ⟨5604506, by rfl⟩ : syracuseStep 7472675 = 11209013) B11209013
theorem B4981783 : Blo 1967435 4981783 := bstep (se 1 (by rfl) ⟨3736337, by rfl⟩ : syracuseStep 4981783 = 7472675) B7472675
theorem B6642377 : Blo 1967435 6642377 := bstep (se 2 (by rfl) ⟨2490891, by rfl⟩ : syracuseStep 6642377 = 4981783) B4981783
theorem B4428251 : Blo 1967435 4428251 := bstep (se 1 (by rfl) ⟨3321188, by rfl⟩ : syracuseStep 4428251 = 6642377) B6642377
theorem B2952167 : Blo 1967435 2952167 := bstep (se 1 (by rfl) ⟨2214125, by rfl⟩ : syracuseStep 2952167 = 4428251) B4428251
theorem B1968111 : Blo 1967435 1968111 := bstep (se 1 (by rfl) ⟨1476083, by rfl⟩ : syracuseStep 1968111 = 2952167) B2952167
theorem B2952173 : Blo 1967435 2952173 := bbase (se 3 (by rfl) ⟨553532, by rfl⟩ : syracuseStep 2952173 = 1107065) (by norm_num)
theorem B1968115 : Blo 1967435 1968115 := bstep (se 1 (by rfl) ⟨1476086, by rfl⟩ : syracuseStep 1968115 = 2952173) B2952173
theorem B4428269 : Blo 1967435 4428269 := bbase (se 3 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 4428269 = 1660601) (by norm_num)
theorem B2952179 : Blo 1967435 2952179 := bstep (se 1 (by rfl) ⟨2214134, by rfl⟩ : syracuseStep 2952179 = 4428269) B4428269
theorem B1968119 : Blo 1967435 1968119 := bstep (se 1 (by rfl) ⟨1476089, by rfl⟩ : syracuseStep 1968119 = 2952179) B2952179
theorem B1994977 : Blo 1967435 1994977 := bbase (se 2 (by rfl) ⟨748116, by rfl⟩ : syracuseStep 1994977 = 1496233) (by norm_num)
theorem B2659969 : Blo 1967435 2659969 := bstep (se 2 (by rfl) ⟨997488, by rfl⟩ : syracuseStep 2659969 = 1994977) B1994977
theorem B14186501 : Blo 1967435 14186501 := bstep (se 4 (by rfl) ⟨1329984, by rfl⟩ : syracuseStep 14186501 = 2659969) B2659969
theorem B9457667 : Blo 1967435 9457667 := bstep (se 1 (by rfl) ⟨7093250, by rfl⟩ : syracuseStep 9457667 = 14186501) B14186501
theorem B6305111 : Blo 1967435 6305111 := bstep (se 1 (by rfl) ⟨4728833, by rfl⟩ : syracuseStep 6305111 = 9457667) B9457667
theorem B4203407 : Blo 1967435 4203407 := bstep (se 1 (by rfl) ⟨3152555, by rfl⟩ : syracuseStep 4203407 = 6305111) B6305111
theorem B2802271 : Blo 1967435 2802271 := bstep (se 1 (by rfl) ⟨2101703, by rfl⟩ : syracuseStep 2802271 = 4203407) B4203407
theorem B3736361 : Blo 1967435 3736361 := bstep (se 2 (by rfl) ⟨1401135, by rfl⟩ : syracuseStep 3736361 = 2802271) B2802271
theorem B2490907 : Blo 1967435 2490907 := bstep (se 1 (by rfl) ⟨1868180, by rfl⟩ : syracuseStep 2490907 = 3736361) B3736361
theorem B3321209 : Blo 1967435 3321209 := bstep (se 2 (by rfl) ⟨1245453, by rfl⟩ : syracuseStep 3321209 = 2490907) B2490907
theorem B2214139 : Blo 1967435 2214139 := bstep (se 1 (by rfl) ⟨1660604, by rfl⟩ : syracuseStep 2214139 = 3321209) B3321209
theorem B2952185 : Blo 1967435 2952185 := bstep (se 2 (by rfl) ⟨1107069, by rfl⟩ : syracuseStep 2952185 = 2214139) B2214139
theorem B1968123 : Blo 1967435 1968123 := bstep (se 1 (by rfl) ⟨1476092, by rfl⟩ : syracuseStep 1968123 = 2952185) B2952185
theorem B16177589 : Blo 1967435 16177589 := bbase (se 5 (by rfl) ⟨758324, by rfl⟩ : syracuseStep 16177589 = 1516649) (by norm_num)
theorem B10785059 : Blo 1967435 10785059 := bstep (se 1 (by rfl) ⟨8088794, by rfl⟩ : syracuseStep 10785059 = 16177589) B16177589
theorem B7190039 : Blo 1967435 7190039 := bstep (se 1 (by rfl) ⟨5392529, by rfl⟩ : syracuseStep 7190039 = 10785059) B10785059
theorem B4793359 : Blo 1967435 4793359 := bstep (se 1 (by rfl) ⟨3595019, by rfl⟩ : syracuseStep 4793359 = 7190039) B7190039
theorem B6391145 : Blo 1967435 6391145 := bstep (se 2 (by rfl) ⟨2396679, by rfl⟩ : syracuseStep 6391145 = 4793359) B4793359
theorem B4260763 : Blo 1967435 4260763 := bstep (se 1 (by rfl) ⟨3195572, by rfl⟩ : syracuseStep 4260763 = 6391145) B6391145
theorem B5681017 : Blo 1967435 5681017 := bstep (se 2 (by rfl) ⟨2130381, by rfl⟩ : syracuseStep 5681017 = 4260763) B4260763
theorem B7574689 : Blo 1967435 7574689 := bstep (se 2 (by rfl) ⟨2840508, by rfl⟩ : syracuseStep 7574689 = 5681017) B5681017
theorem B10099585 : Blo 1967435 10099585 := bstep (se 2 (by rfl) ⟨3787344, by rfl⟩ : syracuseStep 10099585 = 7574689) B7574689
theorem B53864453 : Blo 1967435 53864453 := bstep (se 4 (by rfl) ⟨5049792, by rfl⟩ : syracuseStep 53864453 = 10099585) B10099585
theorem B35909635 : Blo 1967435 35909635 := bstep (se 1 (by rfl) ⟨26932226, by rfl⟩ : syracuseStep 35909635 = 53864453) B53864453
theorem B47879513 : Blo 1967435 47879513 := bstep (se 2 (by rfl) ⟨17954817, by rfl⟩ : syracuseStep 47879513 = 35909635) B35909635
theorem B31919675 : Blo 1967435 31919675 := bstep (se 1 (by rfl) ⟨23939756, by rfl⟩ : syracuseStep 31919675 = 47879513) B47879513
theorem B85119133 : Blo 1967435 85119133 := bstep (se 3 (by rfl) ⟨15959837, by rfl⟩ : syracuseStep 85119133 = 31919675) B31919675
theorem B113492177 : Blo 1967435 113492177 := bstep (se 2 (by rfl) ⟨42559566, by rfl⟩ : syracuseStep 113492177 = 85119133) B85119133
theorem B75661451 : Blo 1967435 75661451 := bstep (se 1 (by rfl) ⟨56746088, by rfl⟩ : syracuseStep 75661451 = 113492177) B113492177
theorem B50440967 : Blo 1967435 50440967 := bstep (se 1 (by rfl) ⟨37830725, by rfl⟩ : syracuseStep 50440967 = 75661451) B75661451
theorem B33627311 : Blo 1967435 33627311 := bstep (se 1 (by rfl) ⟨25220483, by rfl⟩ : syracuseStep 33627311 = 50440967) B50440967
theorem B22418207 : Blo 1967435 22418207 := bstep (se 1 (by rfl) ⟨16813655, by rfl⟩ : syracuseStep 22418207 = 33627311) B33627311
theorem B14945471 : Blo 1967435 14945471 := bstep (se 1 (by rfl) ⟨11209103, by rfl⟩ : syracuseStep 14945471 = 22418207) B22418207
theorem B9963647 : Blo 1967435 9963647 := bstep (se 1 (by rfl) ⟨7472735, by rfl⟩ : syracuseStep 9963647 = 14945471) B14945471
theorem B6642431 : Blo 1967435 6642431 := bstep (se 1 (by rfl) ⟨4981823, by rfl⟩ : syracuseStep 6642431 = 9963647) B9963647
theorem B4428287 : Blo 1967435 4428287 := bstep (se 1 (by rfl) ⟨3321215, by rfl⟩ : syracuseStep 4428287 = 6642431) B6642431
theorem B2952191 : Blo 1967435 2952191 := bstep (se 1 (by rfl) ⟨2214143, by rfl⟩ : syracuseStep 2952191 = 4428287) B4428287
theorem B1968127 : Blo 1967435 1968127 := bstep (se 1 (by rfl) ⟨1476095, by rfl⟩ : syracuseStep 1968127 = 2952191) B2952191
theorem B2952197 : Blo 1967435 2952197 := bbase (se 4 (by rfl) ⟨276768, by rfl⟩ : syracuseStep 2952197 = 553537) (by norm_num)
theorem B1968131 : Blo 1967435 1968131 := bstep (se 1 (by rfl) ⟨1476098, by rfl⟩ : syracuseStep 1968131 = 2952197) B2952197
theorem B3321229 : Blo 1967435 3321229 := bbase (se 3 (by rfl) ⟨622730, by rfl⟩ : syracuseStep 3321229 = 1245461) (by norm_num)
theorem B4428305 : Blo 1967435 4428305 := bstep (se 2 (by rfl) ⟨1660614, by rfl⟩ : syracuseStep 4428305 = 3321229) B3321229
theorem B2952203 : Blo 1967435 2952203 := bstep (se 1 (by rfl) ⟨2214152, by rfl⟩ : syracuseStep 2952203 = 4428305) B4428305
theorem B1968135 : Blo 1967435 1968135 := bstep (se 1 (by rfl) ⟨1476101, by rfl⟩ : syracuseStep 1968135 = 2952203) B2952203
theorem B2214157 : Blo 1967435 2214157 := bbase (se 3 (by rfl) ⟨415154, by rfl⟩ : syracuseStep 2214157 = 830309) (by norm_num)
theorem B2952209 : Blo 1967435 2952209 := bstep (se 2 (by rfl) ⟨1107078, by rfl⟩ : syracuseStep 2952209 = 2214157) B2214157
theorem B1968139 : Blo 1967435 1968139 := bstep (se 1 (by rfl) ⟨1476104, by rfl⟩ : syracuseStep 1968139 = 2952209) B2952209
theorem B6642485 : Blo 1967435 6642485 := bbase (se 5 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 6642485 = 622733) (by norm_num)
theorem B4428323 : Blo 1967435 4428323 := bstep (se 1 (by rfl) ⟨3321242, by rfl⟩ : syracuseStep 4428323 = 6642485) B6642485
theorem B2952215 : Blo 1967435 2952215 := bstep (se 1 (by rfl) ⟨2214161, by rfl⟩ : syracuseStep 2952215 = 4428323) B4428323
theorem B1968143 : Blo 1967435 1968143 := bstep (se 1 (by rfl) ⟨1476107, by rfl⟩ : syracuseStep 1968143 = 2952215) B2952215
theorem B2952221 : Blo 1967435 2952221 := bbase (se 3 (by rfl) ⟨553541, by rfl⟩ : syracuseStep 2952221 = 1107083) (by norm_num)
theorem B1968147 : Blo 1967435 1968147 := bstep (se 1 (by rfl) ⟨1476110, by rfl⟩ : syracuseStep 1968147 = 2952221) B2952221
theorem B4428341 : Blo 1967435 4428341 := bbase (se 5 (by rfl) ⟨207578, by rfl⟩ : syracuseStep 4428341 = 415157) (by norm_num)
theorem B2952227 : Blo 1967435 2952227 := bstep (se 1 (by rfl) ⟨2214170, by rfl⟩ : syracuseStep 2952227 = 4428341) B4428341
theorem B1968151 : Blo 1967435 1968151 := bstep (se 1 (by rfl) ⟨1476113, by rfl⟩ : syracuseStep 1968151 = 2952227) B2952227
theorem B8406949 : Blo 1967435 8406949 := bbase (se 4 (by rfl) ⟨788151, by rfl⟩ : syracuseStep 8406949 = 1576303) (by norm_num)
theorem B11209265 : Blo 1967435 11209265 := bstep (se 2 (by rfl) ⟨4203474, by rfl⟩ : syracuseStep 11209265 = 8406949) B8406949
theorem B7472843 : Blo 1967435 7472843 := bstep (se 1 (by rfl) ⟨5604632, by rfl⟩ : syracuseStep 7472843 = 11209265) B11209265
theorem B4981895 : Blo 1967435 4981895 := bstep (se 1 (by rfl) ⟨3736421, by rfl⟩ : syracuseStep 4981895 = 7472843) B7472843
theorem B3321263 : Blo 1967435 3321263 := bstep (se 1 (by rfl) ⟨2490947, by rfl⟩ : syracuseStep 3321263 = 4981895) B4981895
theorem B2214175 : Blo 1967435 2214175 := bstep (se 1 (by rfl) ⟨1660631, by rfl⟩ : syracuseStep 2214175 = 3321263) B3321263
theorem B2952233 : Blo 1967435 2952233 := bstep (se 2 (by rfl) ⟨1107087, by rfl⟩ : syracuseStep 2952233 = 2214175) B2214175
theorem B1968155 : Blo 1967435 1968155 := bstep (se 1 (by rfl) ⟨1476116, by rfl⟩ : syracuseStep 1968155 = 2952233) B2952233
theorem B8406965 : Blo 1967435 8406965 := bbase (se 5 (by rfl) ⟨394076, by rfl⟩ : syracuseStep 8406965 = 788153) (by norm_num)
theorem B5604643 : Blo 1967435 5604643 := bstep (se 1 (by rfl) ⟨4203482, by rfl⟩ : syracuseStep 5604643 = 8406965) B8406965
theorem B7472857 : Blo 1967435 7472857 := bstep (se 2 (by rfl) ⟨2802321, by rfl⟩ : syracuseStep 7472857 = 5604643) B5604643
theorem B9963809 : Blo 1967435 9963809 := bstep (se 2 (by rfl) ⟨3736428, by rfl⟩ : syracuseStep 9963809 = 7472857) B7472857
theorem B6642539 : Blo 1967435 6642539 := bstep (se 1 (by rfl) ⟨4981904, by rfl⟩ : syracuseStep 6642539 = 9963809) B9963809
theorem B4428359 : Blo 1967435 4428359 := bstep (se 1 (by rfl) ⟨3321269, by rfl⟩ : syracuseStep 4428359 = 6642539) B6642539
theorem B2952239 : Blo 1967435 2952239 := bstep (se 1 (by rfl) ⟨2214179, by rfl⟩ : syracuseStep 2952239 = 4428359) B4428359
theorem B1968159 : Blo 1967435 1968159 := bstep (se 1 (by rfl) ⟨1476119, by rfl⟩ : syracuseStep 1968159 = 2952239) B2952239
theorem B2952245 : Blo 1967435 2952245 := bbase (se 5 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 2952245 = 276773) (by norm_num)
theorem B1968163 : Blo 1967435 1968163 := bstep (se 1 (by rfl) ⟨1476122, by rfl⟩ : syracuseStep 1968163 = 2952245) B2952245
theorem B4981925 : Blo 1967435 4981925 := bbase (se 4 (by rfl) ⟨467055, by rfl⟩ : syracuseStep 4981925 = 934111) (by norm_num)
theorem B3321283 : Blo 1967435 3321283 := bstep (se 1 (by rfl) ⟨2490962, by rfl⟩ : syracuseStep 3321283 = 4981925) B4981925
theorem B4428377 : Blo 1967435 4428377 := bstep (se 2 (by rfl) ⟨1660641, by rfl⟩ : syracuseStep 4428377 = 3321283) B3321283
theorem B2952251 : Blo 1967435 2952251 := bstep (se 1 (by rfl) ⟨2214188, by rfl⟩ : syracuseStep 2952251 = 4428377) B4428377
theorem B1968167 : Blo 1967435 1968167 := bstep (se 1 (by rfl) ⟨1476125, by rfl⟩ : syracuseStep 1968167 = 2952251) B2952251
theorem B2214193 : Blo 1967435 2214193 := bbase (se 2 (by rfl) ⟨830322, by rfl⟩ : syracuseStep 2214193 = 1660645) (by norm_num)
theorem B2952257 : Blo 1967435 2952257 := bstep (se 2 (by rfl) ⟨1107096, by rfl⟩ : syracuseStep 2952257 = 2214193) B2214193
theorem B1968171 : Blo 1967435 1968171 := bstep (se 1 (by rfl) ⟨1476128, by rfl⟩ : syracuseStep 1968171 = 2952257) B2952257
theorem B4203517 : Blo 1967435 4203517 := bbase (se 3 (by rfl) ⟨788159, by rfl⟩ : syracuseStep 4203517 = 1576319) (by norm_num)
theorem B5604689 : Blo 1967435 5604689 := bstep (se 2 (by rfl) ⟨2101758, by rfl⟩ : syracuseStep 5604689 = 4203517) B4203517
theorem B3736459 : Blo 1967435 3736459 := bstep (se 1 (by rfl) ⟨2802344, by rfl⟩ : syracuseStep 3736459 = 5604689) B5604689
theorem B4981945 : Blo 1967435 4981945 := bstep (se 2 (by rfl) ⟨1868229, by rfl⟩ : syracuseStep 4981945 = 3736459) B3736459
theorem B6642593 : Blo 1967435 6642593 := bstep (se 2 (by rfl) ⟨2490972, by rfl⟩ : syracuseStep 6642593 = 4981945) B4981945
theorem B4428395 : Blo 1967435 4428395 := bstep (se 1 (by rfl) ⟨3321296, by rfl⟩ : syracuseStep 4428395 = 6642593) B6642593
theorem B2952263 : Blo 1967435 2952263 := bstep (se 1 (by rfl) ⟨2214197, by rfl⟩ : syracuseStep 2952263 = 4428395) B4428395
theorem B1968175 : Blo 1967435 1968175 := bstep (se 1 (by rfl) ⟨1476131, by rfl⟩ : syracuseStep 1968175 = 2952263) B2952263
theorem B2952269 : Blo 1967435 2952269 := bbase (se 3 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 2952269 = 1107101) (by norm_num)
theorem B1968179 : Blo 1967435 1968179 := bstep (se 1 (by rfl) ⟨1476134, by rfl⟩ : syracuseStep 1968179 = 2952269) B2952269
theorem B4428413 : Blo 1967435 4428413 := bbase (se 3 (by rfl) ⟨830327, by rfl⟩ : syracuseStep 4428413 = 1660655) (by norm_num)
theorem B2952275 : Blo 1967435 2952275 := bstep (se 1 (by rfl) ⟨2214206, by rfl⟩ : syracuseStep 2952275 = 4428413) B4428413
theorem B1968183 : Blo 1967435 1968183 := bstep (se 1 (by rfl) ⟨1476137, by rfl⟩ : syracuseStep 1968183 = 2952275) B2952275
theorem B3321317 : Blo 1967435 3321317 := bbase (se 4 (by rfl) ⟨311373, by rfl⟩ : syracuseStep 3321317 = 622747) (by norm_num)
theorem B2214211 : Blo 1967435 2214211 := bstep (se 1 (by rfl) ⟨1660658, by rfl⟩ : syracuseStep 2214211 = 3321317) B3321317
theorem B2952281 : Blo 1967435 2952281 := bstep (se 2 (by rfl) ⟨1107105, by rfl⟩ : syracuseStep 2952281 = 2214211) B2214211
theorem B1968187 : Blo 1967435 1968187 := bstep (se 1 (by rfl) ⟨1476140, by rfl⟩ : syracuseStep 1968187 = 2952281) B2952281
theorem B3195677 : Blo 1967435 3195677 := bbase (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) (by norm_num)
theorem B8521805 : Blo 1967435 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B22724813 : Blo 1967435 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B60599501 : Blo 1967435 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B40399667 : Blo 1967435 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B26933111 : Blo 1967435 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B17955407 : Blo 1967435 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B11970271 : Blo 1967435 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B15960361 : Blo 1967435 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B21280481 : Blo 1967435 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B14186987 : Blo 1967435 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B9457991 : Blo 1967435 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B6305327 : Blo 1967435 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B4203551 : Blo 1967435 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B2802367 : Blo 1967435 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B14945957 : Blo 1967435 14945957 := bstep (se 4 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 14945957 = 2802367) B2802367
theorem B9963971 : Blo 1967435 9963971 := bstep (se 1 (by rfl) ⟨7472978, by rfl⟩ : syracuseStep 9963971 = 14945957) B14945957
theorem B6642647 : Blo 1967435 6642647 := bstep (se 1 (by rfl) ⟨4981985, by rfl⟩ : syracuseStep 6642647 = 9963971) B9963971
theorem B4428431 : Blo 1967435 4428431 := bstep (se 1 (by rfl) ⟨3321323, by rfl⟩ : syracuseStep 4428431 = 6642647) B6642647
theorem B2952287 : Blo 1967435 2952287 := bstep (se 1 (by rfl) ⟨2214215, by rfl⟩ : syracuseStep 2952287 = 4428431) B4428431
theorem B1968191 : Blo 1967435 1968191 := bstep (se 1 (by rfl) ⟨1476143, by rfl⟩ : syracuseStep 1968191 = 2952287) B2952287
theorem B2952293 : Blo 1967435 2952293 := bbase (se 4 (by rfl) ⟨276777, by rfl⟩ : syracuseStep 2952293 = 553555) (by norm_num)
theorem B1968195 : Blo 1967435 1968195 := bstep (se 1 (by rfl) ⟨1476146, by rfl⟩ : syracuseStep 1968195 = 2952293) B2952293
theorem B3152677 : Blo 1967435 3152677 := bbase (se 4 (by rfl) ⟨295563, by rfl⟩ : syracuseStep 3152677 = 591127) (by norm_num)
theorem B4203569 : Blo 1967435 4203569 := bstep (se 2 (by rfl) ⟨1576338, by rfl⟩ : syracuseStep 4203569 = 3152677) B3152677
theorem B2802379 : Blo 1967435 2802379 := bstep (se 1 (by rfl) ⟨2101784, by rfl⟩ : syracuseStep 2802379 = 4203569) B4203569
theorem B3736505 : Blo 1967435 3736505 := bstep (se 2 (by rfl) ⟨1401189, by rfl⟩ : syracuseStep 3736505 = 2802379) B2802379
theorem B2491003 : Blo 1967435 2491003 := bstep (se 1 (by rfl) ⟨1868252, by rfl⟩ : syracuseStep 2491003 = 3736505) B3736505
theorem B3321337 : Blo 1967435 3321337 := bstep (se 2 (by rfl) ⟨1245501, by rfl⟩ : syracuseStep 3321337 = 2491003) B2491003
theorem B4428449 : Blo 1967435 4428449 := bstep (se 2 (by rfl) ⟨1660668, by rfl⟩ : syracuseStep 4428449 = 3321337) B3321337
theorem B2952299 : Blo 1967435 2952299 := bstep (se 1 (by rfl) ⟨2214224, by rfl⟩ : syracuseStep 2952299 = 4428449) B4428449
theorem B1968199 : Blo 1967435 1968199 := bstep (se 1 (by rfl) ⟨1476149, by rfl⟩ : syracuseStep 1968199 = 2952299) B2952299
theorem B2214229 : Blo 1967435 2214229 := bbase (se 10 (by rfl) ⟨3243, by rfl⟩ : syracuseStep 2214229 = 6487) (by norm_num)
theorem B2952305 : Blo 1967435 2952305 := bstep (se 2 (by rfl) ⟨1107114, by rfl⟩ : syracuseStep 2952305 = 2214229) B2214229
theorem B1968203 : Blo 1967435 1968203 := bstep (se 1 (by rfl) ⟨1476152, by rfl⟩ : syracuseStep 1968203 = 2952305) B2952305
theorem B2491013 : Blo 1967435 2491013 := bbase (se 4 (by rfl) ⟨233532, by rfl⟩ : syracuseStep 2491013 = 467065) (by norm_num)
theorem B6642701 : Blo 1967435 6642701 := bstep (se 3 (by rfl) ⟨1245506, by rfl⟩ : syracuseStep 6642701 = 2491013) B2491013
theorem B4428467 : Blo 1967435 4428467 := bstep (se 1 (by rfl) ⟨3321350, by rfl⟩ : syracuseStep 4428467 = 6642701) B6642701
theorem B2952311 : Blo 1967435 2952311 := bstep (se 1 (by rfl) ⟨2214233, by rfl⟩ : syracuseStep 2952311 = 4428467) B4428467
theorem B1968207 : Blo 1967435 1968207 := bstep (se 1 (by rfl) ⟨1476155, by rfl⟩ : syracuseStep 1968207 = 2952311) B2952311
theorem B2952317 : Blo 1967435 2952317 := bbase (se 3 (by rfl) ⟨553559, by rfl⟩ : syracuseStep 2952317 = 1107119) (by norm_num)
theorem B1968211 : Blo 1967435 1968211 := bstep (se 1 (by rfl) ⟨1476158, by rfl⟩ : syracuseStep 1968211 = 2952317) B2952317
theorem B4428485 : Blo 1967435 4428485 := bbase (se 4 (by rfl) ⟨415170, by rfl⟩ : syracuseStep 4428485 = 830341) (by norm_num)
theorem B2952323 : Blo 1967435 2952323 := bstep (se 1 (by rfl) ⟨2214242, by rfl⟩ : syracuseStep 2952323 = 4428485) B4428485
theorem B1968215 : Blo 1967435 1968215 := bstep (se 1 (by rfl) ⟨1476161, by rfl⟩ : syracuseStep 1968215 = 2952323) B2952323
theorem B3595189 : Blo 1967435 3595189 := bbase (se 5 (by rfl) ⟨168524, by rfl⟩ : syracuseStep 3595189 = 337049) (by norm_num)
theorem B4793585 : Blo 1967435 4793585 := bstep (se 2 (by rfl) ⟨1797594, by rfl⟩ : syracuseStep 4793585 = 3595189) B3595189
theorem B12782893 : Blo 1967435 12782893 := bstep (se 3 (by rfl) ⟨2396792, by rfl⟩ : syracuseStep 12782893 = 4793585) B4793585
theorem B17043857 : Blo 1967435 17043857 := bstep (se 2 (by rfl) ⟨6391446, by rfl⟩ : syracuseStep 17043857 = 12782893) B12782893
theorem B11362571 : Blo 1967435 11362571 := bstep (se 1 (by rfl) ⟨8521928, by rfl⟩ : syracuseStep 11362571 = 17043857) B17043857
theorem B7575047 : Blo 1967435 7575047 := bstep (se 1 (by rfl) ⟨5681285, by rfl⟩ : syracuseStep 7575047 = 11362571) B11362571
theorem B5050031 : Blo 1967435 5050031 := bstep (se 1 (by rfl) ⟨3787523, by rfl⟩ : syracuseStep 5050031 = 7575047) B7575047
theorem B13466749 : Blo 1967435 13466749 := bstep (se 3 (by rfl) ⟨2525015, by rfl⟩ : syracuseStep 13466749 = 5050031) B5050031
theorem B17955665 : Blo 1967435 17955665 := bstep (se 2 (by rfl) ⟨6733374, by rfl⟩ : syracuseStep 17955665 = 13466749) B13466749
theorem B11970443 : Blo 1967435 11970443 := bstep (se 1 (by rfl) ⟨8977832, by rfl⟩ : syracuseStep 11970443 = 17955665) B17955665
theorem B7980295 : Blo 1967435 7980295 := bstep (se 1 (by rfl) ⟨5985221, by rfl⟩ : syracuseStep 7980295 = 11970443) B11970443
theorem B10640393 : Blo 1967435 10640393 := bstep (se 2 (by rfl) ⟨3990147, by rfl⟩ : syracuseStep 10640393 = 7980295) B7980295
theorem B7093595 : Blo 1967435 7093595 := bstep (se 1 (by rfl) ⟨5320196, by rfl⟩ : syracuseStep 7093595 = 10640393) B10640393
theorem B18916253 : Blo 1967435 18916253 := bstep (se 3 (by rfl) ⟨3546797, by rfl⟩ : syracuseStep 18916253 = 7093595) B7093595
theorem B12610835 : Blo 1967435 12610835 := bstep (se 1 (by rfl) ⟨9458126, by rfl⟩ : syracuseStep 12610835 = 18916253) B18916253
theorem B8407223 : Blo 1967435 8407223 := bstep (se 1 (by rfl) ⟨6305417, by rfl⟩ : syracuseStep 8407223 = 12610835) B12610835
theorem B5604815 : Blo 1967435 5604815 := bstep (se 1 (by rfl) ⟨4203611, by rfl⟩ : syracuseStep 5604815 = 8407223) B8407223
theorem B3736543 : Blo 1967435 3736543 := bstep (se 1 (by rfl) ⟨2802407, by rfl⟩ : syracuseStep 3736543 = 5604815) B5604815
theorem B4982057 : Blo 1967435 4982057 := bstep (se 2 (by rfl) ⟨1868271, by rfl⟩ : syracuseStep 4982057 = 3736543) B3736543
theorem B3321371 : Blo 1967435 3321371 := bstep (se 1 (by rfl) ⟨2491028, by rfl⟩ : syracuseStep 3321371 = 4982057) B4982057
theorem B2214247 : Blo 1967435 2214247 := bstep (se 1 (by rfl) ⟨1660685, by rfl⟩ : syracuseStep 2214247 = 3321371) B3321371
theorem B2952329 : Blo 1967435 2952329 := bstep (se 2 (by rfl) ⟨1107123, by rfl⟩ : syracuseStep 2952329 = 2214247) B2214247
theorem B1968219 : Blo 1967435 1968219 := bstep (se 1 (by rfl) ⟨1476164, by rfl⟩ : syracuseStep 1968219 = 2952329) B2952329
theorem B9964133 : Blo 1967435 9964133 := bbase (se 4 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 9964133 = 1868275) (by norm_num)
theorem B6642755 : Blo 1967435 6642755 := bstep (se 1 (by rfl) ⟨4982066, by rfl⟩ : syracuseStep 6642755 = 9964133) B9964133
theorem B4428503 : Blo 1967435 4428503 := bstep (se 1 (by rfl) ⟨3321377, by rfl⟩ : syracuseStep 4428503 = 6642755) B6642755
theorem B2952335 : Blo 1967435 2952335 := bstep (se 1 (by rfl) ⟨2214251, by rfl⟩ : syracuseStep 2952335 = 4428503) B4428503
theorem B1968223 : Blo 1967435 1968223 := bstep (se 1 (by rfl) ⟨1476167, by rfl⟩ : syracuseStep 1968223 = 2952335) B2952335
theorem B2952341 : Blo 1967435 2952341 := bbase (se 6 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 2952341 = 138391) (by norm_num)
theorem B1968227 : Blo 1967435 1968227 := bstep (se 1 (by rfl) ⟨1476170, by rfl⟩ : syracuseStep 1968227 = 2952341) B2952341
theorem B2559481 : Blo 1967435 2559481 := bbase (se 2 (by rfl) ⟨959805, by rfl⟩ : syracuseStep 2559481 = 1919611) (by norm_num)
theorem B54602261 : Blo 1967435 54602261 := bstep (se 6 (by rfl) ⟨1279740, by rfl⟩ : syracuseStep 54602261 = 2559481) B2559481
theorem B36401507 : Blo 1967435 36401507 := bstep (se 1 (by rfl) ⟨27301130, by rfl⟩ : syracuseStep 36401507 = 54602261) B54602261
theorem B24267671 : Blo 1967435 24267671 := bstep (se 1 (by rfl) ⟨18200753, by rfl⟩ : syracuseStep 24267671 = 36401507) B36401507
theorem B16178447 : Blo 1967435 16178447 := bstep (se 1 (by rfl) ⟨12133835, by rfl⟩ : syracuseStep 16178447 = 24267671) B24267671
theorem B10785631 : Blo 1967435 10785631 := bstep (se 1 (by rfl) ⟨8089223, by rfl⟩ : syracuseStep 10785631 = 16178447) B16178447
theorem B14380841 : Blo 1967435 14380841 := bstep (se 2 (by rfl) ⟨5392815, by rfl⟩ : syracuseStep 14380841 = 10785631) B10785631
theorem B38348909 : Blo 1967435 38348909 := bstep (se 3 (by rfl) ⟨7190420, by rfl⟩ : syracuseStep 38348909 = 14380841) B14380841
theorem B25565939 : Blo 1967435 25565939 := bstep (se 1 (by rfl) ⟨19174454, by rfl⟩ : syracuseStep 25565939 = 38348909) B38348909
theorem B17043959 : Blo 1967435 17043959 := bstep (se 1 (by rfl) ⟨12782969, by rfl⟩ : syracuseStep 17043959 = 25565939) B25565939
theorem B11362639 : Blo 1967435 11362639 := bstep (se 1 (by rfl) ⟨8521979, by rfl⟩ : syracuseStep 11362639 = 17043959) B17043959
theorem B15150185 : Blo 1967435 15150185 := bstep (se 2 (by rfl) ⟨5681319, by rfl⟩ : syracuseStep 15150185 = 11362639) B11362639
theorem B10100123 : Blo 1967435 10100123 := bstep (se 1 (by rfl) ⟨7575092, by rfl⟩ : syracuseStep 10100123 = 15150185) B15150185
theorem B6733415 : Blo 1967435 6733415 := bstep (se 1 (by rfl) ⟨5050061, by rfl⟩ : syracuseStep 6733415 = 10100123) B10100123
theorem B4488943 : Blo 1967435 4488943 := bstep (se 1 (by rfl) ⟨3366707, by rfl⟩ : syracuseStep 4488943 = 6733415) B6733415
theorem B5985257 : Blo 1967435 5985257 := bstep (se 2 (by rfl) ⟨2244471, by rfl⟩ : syracuseStep 5985257 = 4488943) B4488943
theorem B15960685 : Blo 1967435 15960685 := bstep (se 3 (by rfl) ⟨2992628, by rfl⟩ : syracuseStep 15960685 = 5985257) B5985257
theorem B21280913 : Blo 1967435 21280913 := bstep (se 2 (by rfl) ⟨7980342, by rfl⟩ : syracuseStep 21280913 = 15960685) B15960685
theorem B14187275 : Blo 1967435 14187275 := bstep (se 1 (by rfl) ⟨10640456, by rfl⟩ : syracuseStep 14187275 = 21280913) B21280913
theorem B9458183 : Blo 1967435 9458183 := bstep (se 1 (by rfl) ⟨7093637, by rfl⟩ : syracuseStep 9458183 = 14187275) B14187275
theorem B6305455 : Blo 1967435 6305455 := bstep (se 1 (by rfl) ⟨4729091, by rfl⟩ : syracuseStep 6305455 = 9458183) B9458183
theorem B8407273 : Blo 1967435 8407273 := bstep (se 2 (by rfl) ⟨3152727, by rfl⟩ : syracuseStep 8407273 = 6305455) B6305455
theorem B11209697 : Blo 1967435 11209697 := bstep (se 2 (by rfl) ⟨4203636, by rfl⟩ : syracuseStep 11209697 = 8407273) B8407273
theorem B7473131 : Blo 1967435 7473131 := bstep (se 1 (by rfl) ⟨5604848, by rfl⟩ : syracuseStep 7473131 = 11209697) B11209697
theorem B4982087 : Blo 1967435 4982087 := bstep (se 1 (by rfl) ⟨3736565, by rfl⟩ : syracuseStep 4982087 = 7473131) B7473131
theorem B3321391 : Blo 1967435 3321391 := bstep (se 1 (by rfl) ⟨2491043, by rfl⟩ : syracuseStep 3321391 = 4982087) B4982087
theorem B4428521 : Blo 1967435 4428521 := bstep (se 2 (by rfl) ⟨1660695, by rfl⟩ : syracuseStep 4428521 = 3321391) B3321391
theorem B2952347 : Blo 1967435 2952347 := bstep (se 1 (by rfl) ⟨2214260, by rfl⟩ : syracuseStep 2952347 = 4428521) B4428521
theorem B1968231 : Blo 1967435 1968231 := bstep (se 1 (by rfl) ⟨1476173, by rfl⟩ : syracuseStep 1968231 = 2952347) B2952347
theorem B2214265 : Blo 1967435 2214265 := bbase (se 2 (by rfl) ⟨830349, by rfl⟩ : syracuseStep 2214265 = 1660699) (by norm_num)
theorem B2952353 : Blo 1967435 2952353 := bstep (se 2 (by rfl) ⟨1107132, by rfl⟩ : syracuseStep 2952353 = 2214265) B2214265
theorem B1968235 : Blo 1967435 1968235 := bstep (se 1 (by rfl) ⟨1476176, by rfl⟩ : syracuseStep 1968235 = 2952353) B2952353
theorem B2660125 : Blo 1967435 2660125 := bbase (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) (by norm_num)
theorem B3546833 : Blo 1967435 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B9458221 : Blo 1967435 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B12610961 : Blo 1967435 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B8407307 : Blo 1967435 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B5604871 : Blo 1967435 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B7473161 : Blo 1967435 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B4982107 : Blo 1967435 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B6642809 : Blo 1967435 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B4428539 : Blo 1967435 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B2952359 : Blo 1967435 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B1968239 : Blo 1967435 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B2952365 : Blo 1967435 2952365 := bbase (se 3 (by rfl) ⟨553568, by rfl⟩ : syracuseStep 2952365 = 1107137) (by norm_num)
theorem B1968243 : Blo 1967435 1968243 := bstep (se 1 (by rfl) ⟨1476182, by rfl⟩ : syracuseStep 1968243 = 2952365) B2952365
theorem B4428557 : Blo 1967435 4428557 := bbase (se 3 (by rfl) ⟨830354, by rfl⟩ : syracuseStep 4428557 = 1660709) (by norm_num)
theorem B2952371 : Blo 1967435 2952371 := bstep (se 1 (by rfl) ⟨2214278, by rfl⟩ : syracuseStep 2952371 = 4428557) B4428557
theorem B1968247 : Blo 1967435 1968247 := bstep (se 1 (by rfl) ⟨1476185, by rfl⟩ : syracuseStep 1968247 = 2952371) B2952371
theorem B2491069 : Blo 1967435 2491069 := bbase (se 3 (by rfl) ⟨467075, by rfl⟩ : syracuseStep 2491069 = 934151) (by norm_num)
theorem B3321425 : Blo 1967435 3321425 := bstep (se 2 (by rfl) ⟨1245534, by rfl⟩ : syracuseStep 3321425 = 2491069) B2491069
theorem B2214283 : Blo 1967435 2214283 := bstep (se 1 (by rfl) ⟨1660712, by rfl⟩ : syracuseStep 2214283 = 3321425) B3321425
theorem B2952377 : Blo 1967435 2952377 := bstep (se 2 (by rfl) ⟨1107141, by rfl⟩ : syracuseStep 2952377 = 2214283) B2214283
theorem B1968251 : Blo 1967435 1968251 := bstep (se 1 (by rfl) ⟨1476188, by rfl⟩ : syracuseStep 1968251 = 2952377) B2952377
theorem B17955989 : Blo 1967435 17955989 := bbase (se 6 (by rfl) ⟨420843, by rfl⟩ : syracuseStep 17955989 = 841687) (by norm_num)
theorem B11970659 : Blo 1967435 11970659 := bstep (se 1 (by rfl) ⟨8977994, by rfl⟩ : syracuseStep 11970659 = 17955989) B17955989
theorem B7980439 : Blo 1967435 7980439 := bstep (se 1 (by rfl) ⟨5985329, by rfl⟩ : syracuseStep 7980439 = 11970659) B11970659
theorem B10640585 : Blo 1967435 10640585 := bstep (se 2 (by rfl) ⟨3990219, by rfl⟩ : syracuseStep 10640585 = 7980439) B7980439
theorem B7093723 : Blo 1967435 7093723 := bstep (se 1 (by rfl) ⟨5320292, by rfl⟩ : syracuseStep 7093723 = 10640585) B10640585
theorem B9458297 : Blo 1967435 9458297 := bstep (se 2 (by rfl) ⟨3546861, by rfl⟩ : syracuseStep 9458297 = 7093723) B7093723
theorem B6305531 : Blo 1967435 6305531 := bstep (se 1 (by rfl) ⟨4729148, by rfl⟩ : syracuseStep 6305531 = 9458297) B9458297
theorem B16814749 : Blo 1967435 16814749 := bstep (se 3 (by rfl) ⟨3152765, by rfl⟩ : syracuseStep 16814749 = 6305531) B6305531
theorem B22419665 : Blo 1967435 22419665 := bstep (se 2 (by rfl) ⟨8407374, by rfl⟩ : syracuseStep 22419665 = 16814749) B16814749
theorem B14946443 : Blo 1967435 14946443 := bstep (se 1 (by rfl) ⟨11209832, by rfl⟩ : syracuseStep 14946443 = 22419665) B22419665
theorem B9964295 : Blo 1967435 9964295 := bstep (se 1 (by rfl) ⟨7473221, by rfl⟩ : syracuseStep 9964295 = 14946443) B14946443
theorem B6642863 : Blo 1967435 6642863 := bstep (se 1 (by rfl) ⟨4982147, by rfl⟩ : syracuseStep 6642863 = 9964295) B9964295
theorem B4428575 : Blo 1967435 4428575 := bstep (se 1 (by rfl) ⟨3321431, by rfl⟩ : syracuseStep 4428575 = 6642863) B6642863
theorem B2952383 : Blo 1967435 2952383 := bstep (se 1 (by rfl) ⟨2214287, by rfl⟩ : syracuseStep 2952383 = 4428575) B4428575
theorem B1968255 : Blo 1967435 1968255 := bstep (se 1 (by rfl) ⟨1476191, by rfl⟩ : syracuseStep 1968255 = 2952383) B2952383
theorem B2952389 : Blo 1967435 2952389 := bbase (se 4 (by rfl) ⟨276786, by rfl⟩ : syracuseStep 2952389 = 553573) (by norm_num)
theorem B1968259 : Blo 1967435 1968259 := bstep (se 1 (by rfl) ⟨1476194, by rfl⟩ : syracuseStep 1968259 = 2952389) B2952389
theorem B3321445 : Blo 1967435 3321445 := bbase (se 4 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 3321445 = 622771) (by norm_num)
theorem B4428593 : Blo 1967435 4428593 := bstep (se 2 (by rfl) ⟨1660722, by rfl⟩ : syracuseStep 4428593 = 3321445) B3321445
theorem B2952395 : Blo 1967435 2952395 := bstep (se 1 (by rfl) ⟨2214296, by rfl⟩ : syracuseStep 2952395 = 4428593) B4428593
theorem B1968263 : Blo 1967435 1968263 := bstep (se 1 (by rfl) ⟨1476197, by rfl⟩ : syracuseStep 1968263 = 2952395) B2952395
theorem B2214301 : Blo 1967435 2214301 := bbase (se 3 (by rfl) ⟨415181, by rfl⟩ : syracuseStep 2214301 = 830363) (by norm_num)
theorem B2952401 : Blo 1967435 2952401 := bstep (se 2 (by rfl) ⟨1107150, by rfl⟩ : syracuseStep 2952401 = 2214301) B2214301
theorem B1968267 : Blo 1967435 1968267 := bstep (se 1 (by rfl) ⟨1476200, by rfl⟩ : syracuseStep 1968267 = 2952401) B2952401
theorem B6642917 : Blo 1967435 6642917 := bbase (se 4 (by rfl) ⟨622773, by rfl⟩ : syracuseStep 6642917 = 1245547) (by norm_num)
theorem B4428611 : Blo 1967435 4428611 := bstep (se 1 (by rfl) ⟨3321458, by rfl⟩ : syracuseStep 4428611 = 6642917) B6642917
theorem B2952407 : Blo 1967435 2952407 := bstep (se 1 (by rfl) ⟨2214305, by rfl⟩ : syracuseStep 2952407 = 4428611) B4428611
theorem B1968271 : Blo 1967435 1968271 := bstep (se 1 (by rfl) ⟨1476203, by rfl⟩ : syracuseStep 1968271 = 2952407) B2952407
theorem B2952413 : Blo 1967435 2952413 := bbase (se 3 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 2952413 = 1107155) (by norm_num)
theorem B1968275 : Blo 1967435 1968275 := bstep (se 1 (by rfl) ⟨1476206, by rfl⟩ : syracuseStep 1968275 = 2952413) B2952413
theorem B4428629 : Blo 1967435 4428629 := bbase (se 9 (by rfl) ⟨12974, by rfl⟩ : syracuseStep 4428629 = 25949) (by norm_num)
theorem B2952419 : Blo 1967435 2952419 := bstep (se 1 (by rfl) ⟨2214314, by rfl⟩ : syracuseStep 2952419 = 4428629) B4428629
theorem B1968279 : Blo 1967435 1968279 := bstep (se 1 (by rfl) ⟨1476209, by rfl⟩ : syracuseStep 1968279 = 2952419) B2952419
theorem B5604997 : Blo 1967435 5604997 := bbase (se 4 (by rfl) ⟨525468, by rfl⟩ : syracuseStep 5604997 = 1050937) (by norm_num)
theorem B7473329 : Blo 1967435 7473329 := bstep (se 2 (by rfl) ⟨2802498, by rfl⟩ : syracuseStep 7473329 = 5604997) B5604997
theorem B4982219 : Blo 1967435 4982219 := bstep (se 1 (by rfl) ⟨3736664, by rfl⟩ : syracuseStep 4982219 = 7473329) B7473329
theorem B3321479 : Blo 1967435 3321479 := bstep (se 1 (by rfl) ⟨2491109, by rfl⟩ : syracuseStep 3321479 = 4982219) B4982219
theorem B2214319 : Blo 1967435 2214319 := bstep (se 1 (by rfl) ⟨1660739, by rfl⟩ : syracuseStep 2214319 = 3321479) B3321479
theorem B2952425 : Blo 1967435 2952425 := bstep (se 2 (by rfl) ⟨1107159, by rfl⟩ : syracuseStep 2952425 = 2214319) B2214319
theorem B1968283 : Blo 1967435 1968283 := bstep (se 1 (by rfl) ⟨1476212, by rfl⟩ : syracuseStep 1968283 = 2952425) B2952425
theorem B42563029 : Blo 1967435 42563029 := bbase (se 7 (by rfl) ⟨498785, by rfl⟩ : syracuseStep 42563029 = 997571) (by norm_num)
theorem B56750705 : Blo 1967435 56750705 := bstep (se 2 (by rfl) ⟨21281514, by rfl⟩ : syracuseStep 56750705 = 42563029) B42563029
theorem B37833803 : Blo 1967435 37833803 := bstep (se 1 (by rfl) ⟨28375352, by rfl⟩ : syracuseStep 37833803 = 56750705) B56750705
theorem B25222535 : Blo 1967435 25222535 := bstep (se 1 (by rfl) ⟨18916901, by rfl⟩ : syracuseStep 25222535 = 37833803) B37833803
theorem B16815023 : Blo 1967435 16815023 := bstep (se 1 (by rfl) ⟨12611267, by rfl⟩ : syracuseStep 16815023 = 25222535) B25222535
theorem B11210015 : Blo 1967435 11210015 := bstep (se 1 (by rfl) ⟨8407511, by rfl⟩ : syracuseStep 11210015 = 16815023) B16815023
theorem B7473343 : Blo 1967435 7473343 := bstep (se 1 (by rfl) ⟨5605007, by rfl⟩ : syracuseStep 7473343 = 11210015) B11210015
theorem B9964457 : Blo 1967435 9964457 := bstep (se 2 (by rfl) ⟨3736671, by rfl⟩ : syracuseStep 9964457 = 7473343) B7473343
theorem B6642971 : Blo 1967435 6642971 := bstep (se 1 (by rfl) ⟨4982228, by rfl⟩ : syracuseStep 6642971 = 9964457) B9964457
theorem B4428647 : Blo 1967435 4428647 := bstep (se 1 (by rfl) ⟨3321485, by rfl⟩ : syracuseStep 4428647 = 6642971) B6642971
theorem B2952431 : Blo 1967435 2952431 := bstep (se 1 (by rfl) ⟨2214323, by rfl⟩ : syracuseStep 2952431 = 4428647) B4428647
theorem B1968287 : Blo 1967435 1968287 := bstep (se 1 (by rfl) ⟨1476215, by rfl⟩ : syracuseStep 1968287 = 2952431) B2952431
theorem B2952437 : Blo 1967435 2952437 := bbase (se 5 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 2952437 = 276791) (by norm_num)
theorem B1968291 : Blo 1967435 1968291 := bstep (se 1 (by rfl) ⟨1476218, by rfl⟩ : syracuseStep 1968291 = 2952437) B2952437
theorem B15961205 : Blo 1967435 15961205 := bbase (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) (by norm_num)
theorem B10640803 : Blo 1967435 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B14187737 : Blo 1967435 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B9458491 : Blo 1967435 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B12611321 : Blo 1967435 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B8407547 : Blo 1967435 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B5605031 : Blo 1967435 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B3736687 : Blo 1967435 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B4982249 : Blo 1967435 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B3321499 : Blo 1967435 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B4428665 : Blo 1967435 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B2952443 : Blo 1967435 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B1968295 : Blo 1967435 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B2214337 : Blo 1967435 2214337 := bbase (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) (by norm_num)
theorem B2952449 : Blo 1967435 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B1968299 : Blo 1967435 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B4982269 : Blo 1967435 4982269 := bbase (se 3 (by rfl) ⟨934175, by rfl⟩ : syracuseStep 4982269 = 1868351) (by norm_num)
theorem B6643025 : Blo 1967435 6643025 := bstep (se 2 (by rfl) ⟨2491134, by rfl⟩ : syracuseStep 6643025 = 4982269) B4982269
theorem B4428683 : Blo 1967435 4428683 := bstep (se 1 (by rfl) ⟨3321512, by rfl⟩ : syracuseStep 4428683 = 6643025) B6643025
theorem B2952455 : Blo 1967435 2952455 := bstep (se 1 (by rfl) ⟨2214341, by rfl⟩ : syracuseStep 2952455 = 4428683) B4428683
theorem B1968303 : Blo 1967435 1968303 := bstep (se 1 (by rfl) ⟨1476227, by rfl⟩ : syracuseStep 1968303 = 2952455) B2952455
theorem B2952461 : Blo 1967435 2952461 := bbase (se 3 (by rfl) ⟨553586, by rfl⟩ : syracuseStep 2952461 = 1107173) (by norm_num)
theorem B1968307 : Blo 1967435 1968307 := bstep (se 1 (by rfl) ⟨1476230, by rfl⟩ : syracuseStep 1968307 = 2952461) B2952461
theorem B4428701 : Blo 1967435 4428701 := bbase (se 3 (by rfl) ⟨830381, by rfl⟩ : syracuseStep 4428701 = 1660763) (by norm_num)
theorem B2952467 : Blo 1967435 2952467 := bstep (se 1 (by rfl) ⟨2214350, by rfl⟩ : syracuseStep 2952467 = 4428701) B4428701
theorem B1968311 : Blo 1967435 1968311 := bstep (se 1 (by rfl) ⟨1476233, by rfl⟩ : syracuseStep 1968311 = 2952467) B2952467
theorem B3321533 : Blo 1967435 3321533 := bbase (se 3 (by rfl) ⟨622787, by rfl⟩ : syracuseStep 3321533 = 1245575) (by norm_num)
theorem B2214355 : Blo 1967435 2214355 := bstep (se 1 (by rfl) ⟨1660766, by rfl⟩ : syracuseStep 2214355 = 3321533) B3321533
theorem B2952473 : Blo 1967435 2952473 := bstep (se 2 (by rfl) ⟨1107177, by rfl⟩ : syracuseStep 2952473 = 2214355) B2214355
theorem B1968315 : Blo 1967435 1968315 := bstep (se 1 (by rfl) ⟨1476236, by rfl⟩ : syracuseStep 1968315 = 2952473) B2952473
theorem B11210197 : Blo 1967435 11210197 := bbase (se 7 (by rfl) ⟨131369, by rfl⟩ : syracuseStep 11210197 = 262739) (by norm_num)
theorem B14946929 : Blo 1967435 14946929 := bstep (se 2 (by rfl) ⟨5605098, by rfl⟩ : syracuseStep 14946929 = 11210197) B11210197
theorem B9964619 : Blo 1967435 9964619 := bstep (se 1 (by rfl) ⟨7473464, by rfl⟩ : syracuseStep 9964619 = 14946929) B14946929
theorem B6643079 : Blo 1967435 6643079 := bstep (se 1 (by rfl) ⟨4982309, by rfl⟩ : syracuseStep 6643079 = 9964619) B9964619
theorem B4428719 : Blo 1967435 4428719 := bstep (se 1 (by rfl) ⟨3321539, by rfl⟩ : syracuseStep 4428719 = 6643079) B6643079
theorem B2952479 : Blo 1967435 2952479 := bstep (se 1 (by rfl) ⟨2214359, by rfl⟩ : syracuseStep 2952479 = 4428719) B4428719
theorem B1968319 : Blo 1967435 1968319 := bstep (se 1 (by rfl) ⟨1476239, by rfl⟩ : syracuseStep 1968319 = 2952479) B2952479
theorem B2952485 : Blo 1967435 2952485 := bbase (se 4 (by rfl) ⟨276795, by rfl⟩ : syracuseStep 2952485 = 553591) (by norm_num)
theorem B1968323 : Blo 1967435 1968323 := bstep (se 1 (by rfl) ⟨1476242, by rfl⟩ : syracuseStep 1968323 = 2952485) B2952485
theorem B2491165 : Blo 1967435 2491165 := bbase (se 3 (by rfl) ⟨467093, by rfl⟩ : syracuseStep 2491165 = 934187) (by norm_num)
theorem B3321553 : Blo 1967435 3321553 := bstep (se 2 (by rfl) ⟨1245582, by rfl⟩ : syracuseStep 3321553 = 2491165) B2491165
theorem B4428737 : Blo 1967435 4428737 := bstep (se 2 (by rfl) ⟨1660776, by rfl⟩ : syracuseStep 4428737 = 3321553) B3321553
theorem B2952491 : Blo 1967435 2952491 := bstep (se 1 (by rfl) ⟨2214368, by rfl⟩ : syracuseStep 2952491 = 4428737) B4428737
theorem B1968327 : Blo 1967435 1968327 := bstep (se 1 (by rfl) ⟨1476245, by rfl⟩ : syracuseStep 1968327 = 2952491) B2952491
theorem B2214373 : Blo 1967435 2214373 := bbase (se 4 (by rfl) ⟨207597, by rfl⟩ : syracuseStep 2214373 = 415195) (by norm_num)
theorem B2952497 : Blo 1967435 2952497 := bstep (se 2 (by rfl) ⟨1107186, by rfl⟩ : syracuseStep 2952497 = 2214373) B2214373
theorem B1968331 : Blo 1967435 1968331 := bstep (se 1 (by rfl) ⟨1476248, by rfl⟩ : syracuseStep 1968331 = 2952497) B2952497
theorem B5681621 : Blo 1967435 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B15150989 : Blo 1967435 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B40402637 : Blo 1967435 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B26935091 : Blo 1967435 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B17956727 : Blo 1967435 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B11971151 : Blo 1967435 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B7980767 : Blo 1967435 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B5320511 : Blo 1967435 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B3547007 : Blo 1967435 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B2364671 : Blo 1967435 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B6305789 : Blo 1967435 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B4203859 : Blo 1967435 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B5605145 : Blo 1967435 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B3736763 : Blo 1967435 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B2491175 : Blo 1967435 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B6643133 : Blo 1967435 6643133 := bstep (se 3 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 6643133 = 2491175) B2491175
theorem B4428755 : Blo 1967435 4428755 := bstep (se 1 (by rfl) ⟨3321566, by rfl⟩ : syracuseStep 4428755 = 6643133) B6643133
theorem B2952503 : Blo 1967435 2952503 := bstep (se 1 (by rfl) ⟨2214377, by rfl⟩ : syracuseStep 2952503 = 4428755) B4428755
theorem B1968335 : Blo 1967435 1968335 := bstep (se 1 (by rfl) ⟨1476251, by rfl⟩ : syracuseStep 1968335 = 2952503) B2952503
theorem B2952509 : Blo 1967435 2952509 := bbase (se 3 (by rfl) ⟨553595, by rfl⟩ : syracuseStep 2952509 = 1107191) (by norm_num)
theorem B1968339 : Blo 1967435 1968339 := bstep (se 1 (by rfl) ⟨1476254, by rfl⟩ : syracuseStep 1968339 = 2952509) B2952509
theorem B4428773 : Blo 1967435 4428773 := bbase (se 4 (by rfl) ⟨415197, by rfl⟩ : syracuseStep 4428773 = 830395) (by norm_num)
theorem B2952515 : Blo 1967435 2952515 := bstep (se 1 (by rfl) ⟨2214386, by rfl⟩ : syracuseStep 2952515 = 4428773) B4428773
theorem B1968343 : Blo 1967435 1968343 := bstep (se 1 (by rfl) ⟨1476257, by rfl⟩ : syracuseStep 1968343 = 2952515) B2952515
theorem B4982381 : Blo 1967435 4982381 := bbase (se 3 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 4982381 = 1868393) (by norm_num)
theorem B3321587 : Blo 1967435 3321587 := bstep (se 1 (by rfl) ⟨2491190, by rfl⟩ : syracuseStep 3321587 = 4982381) B4982381
theorem B2214391 : Blo 1967435 2214391 := bstep (se 1 (by rfl) ⟨1660793, by rfl⟩ : syracuseStep 2214391 = 3321587) B3321587
theorem B2952521 : Blo 1967435 2952521 := bstep (se 2 (by rfl) ⟨1107195, by rfl⟩ : syracuseStep 2952521 = 2214391) B2214391
theorem B1968347 : Blo 1967435 1968347 := bstep (se 1 (by rfl) ⟨1476260, by rfl⟩ : syracuseStep 1968347 = 2952521) B2952521
theorem B4203893 : Blo 1967435 4203893 := bbase (se 5 (by rfl) ⟨197057, by rfl⟩ : syracuseStep 4203893 = 394115) (by norm_num)
theorem B2802595 : Blo 1967435 2802595 := bstep (se 1 (by rfl) ⟨2101946, by rfl⟩ : syracuseStep 2802595 = 4203893) B4203893
theorem B3736793 : Blo 1967435 3736793 := bstep (se 2 (by rfl) ⟨1401297, by rfl⟩ : syracuseStep 3736793 = 2802595) B2802595
theorem B9964781 : Blo 1967435 9964781 := bstep (se 3 (by rfl) ⟨1868396, by rfl⟩ : syracuseStep 9964781 = 3736793) B3736793
theorem B6643187 : Blo 1967435 6643187 := bstep (se 1 (by rfl) ⟨4982390, by rfl⟩ : syracuseStep 6643187 = 9964781) B9964781
theorem B4428791 : Blo 1967435 4428791 := bstep (se 1 (by rfl) ⟨3321593, by rfl⟩ : syracuseStep 4428791 = 6643187) B6643187
theorem B2952527 : Blo 1967435 2952527 := bstep (se 1 (by rfl) ⟨2214395, by rfl⟩ : syracuseStep 2952527 = 4428791) B4428791
theorem B1968351 : Blo 1967435 1968351 := bstep (se 1 (by rfl) ⟨1476263, by rfl⟩ : syracuseStep 1968351 = 2952527) B2952527
theorem B2952533 : Blo 1967435 2952533 := bbase (se 11 (by rfl) ⟨2162, by rfl⟩ : syracuseStep 2952533 = 4325) (by norm_num)
theorem B1968355 : Blo 1967435 1968355 := bstep (se 1 (by rfl) ⟨1476266, by rfl⟩ : syracuseStep 1968355 = 2952533) B2952533
theorem B3152933 : Blo 1967435 3152933 := bbase (se 4 (by rfl) ⟨295587, by rfl⟩ : syracuseStep 3152933 = 591175) (by norm_num)
theorem B2101955 : Blo 1967435 2101955 := bstep (se 1 (by rfl) ⟨1576466, by rfl⟩ : syracuseStep 2101955 = 3152933) B3152933
theorem B5605213 : Blo 1967435 5605213 := bstep (se 3 (by rfl) ⟨1050977, by rfl⟩ : syracuseStep 5605213 = 2101955) B2101955
theorem B7473617 : Blo 1967435 7473617 := bstep (se 2 (by rfl) ⟨2802606, by rfl⟩ : syracuseStep 7473617 = 5605213) B5605213
theorem B4982411 : Blo 1967435 4982411 := bstep (se 1 (by rfl) ⟨3736808, by rfl⟩ : syracuseStep 4982411 = 7473617) B7473617
theorem B3321607 : Blo 1967435 3321607 := bstep (se 1 (by rfl) ⟨2491205, by rfl⟩ : syracuseStep 3321607 = 4982411) B4982411
theorem B4428809 : Blo 1967435 4428809 := bstep (se 2 (by rfl) ⟨1660803, by rfl⟩ : syracuseStep 4428809 = 3321607) B3321607
theorem B2952539 : Blo 1967435 2952539 := bstep (se 1 (by rfl) ⟨2214404, by rfl⟩ : syracuseStep 2952539 = 4428809) B4428809
theorem B1968359 : Blo 1967435 1968359 := bstep (se 1 (by rfl) ⟨1476269, by rfl⟩ : syracuseStep 1968359 = 2952539) B2952539
theorem B2214409 : Blo 1967435 2214409 := bbase (se 2 (by rfl) ⟨830403, by rfl⟩ : syracuseStep 2214409 = 1660807) (by norm_num)
theorem B2952545 : Blo 1967435 2952545 := bstep (se 2 (by rfl) ⟨1107204, by rfl⟩ : syracuseStep 2952545 = 2214409) B2214409
theorem B1968363 : Blo 1967435 1968363 := bstep (se 1 (by rfl) ⟨1476272, by rfl⟩ : syracuseStep 1968363 = 2952545) B2952545
theorem B24600469 : Blo 1967435 24600469 := bbase (se 6 (by rfl) ⟨576573, by rfl⟩ : syracuseStep 24600469 = 1153147) (by norm_num)
theorem B32800625 : Blo 1967435 32800625 := bstep (se 2 (by rfl) ⟨12300234, by rfl⟩ : syracuseStep 32800625 = 24600469) B24600469
theorem B21867083 : Blo 1967435 21867083 := bstep (se 1 (by rfl) ⟨16400312, by rfl⟩ : syracuseStep 21867083 = 32800625) B32800625
theorem B14578055 : Blo 1967435 14578055 := bstep (se 1 (by rfl) ⟨10933541, by rfl⟩ : syracuseStep 14578055 = 21867083) B21867083
theorem B9718703 : Blo 1967435 9718703 := bstep (se 1 (by rfl) ⟨7289027, by rfl⟩ : syracuseStep 9718703 = 14578055) B14578055
theorem B6479135 : Blo 1967435 6479135 := bstep (se 1 (by rfl) ⟨4859351, by rfl⟩ : syracuseStep 6479135 = 9718703) B9718703
theorem B4319423 : Blo 1967435 4319423 := bstep (se 1 (by rfl) ⟨3239567, by rfl⟩ : syracuseStep 4319423 = 6479135) B6479135
theorem B2879615 : Blo 1967435 2879615 := bstep (se 1 (by rfl) ⟨2159711, by rfl⟩ : syracuseStep 2879615 = 4319423) B4319423
theorem B7678973 : Blo 1967435 7678973 := bstep (se 3 (by rfl) ⟨1439807, by rfl⟩ : syracuseStep 7678973 = 2879615) B2879615
theorem B20477261 : Blo 1967435 20477261 := bstep (se 3 (by rfl) ⟨3839486, by rfl⟩ : syracuseStep 20477261 = 7678973) B7678973
theorem B13651507 : Blo 1967435 13651507 := bstep (se 1 (by rfl) ⟨10238630, by rfl⟩ : syracuseStep 13651507 = 20477261) B20477261
theorem B18202009 : Blo 1967435 18202009 := bstep (se 2 (by rfl) ⟨6825753, by rfl⟩ : syracuseStep 18202009 = 13651507) B13651507
theorem B24269345 : Blo 1967435 24269345 := bstep (se 2 (by rfl) ⟨9101004, by rfl⟩ : syracuseStep 24269345 = 18202009) B18202009
theorem B16179563 : Blo 1967435 16179563 := bstep (se 1 (by rfl) ⟨12134672, by rfl⟩ : syracuseStep 16179563 = 24269345) B24269345
theorem B10786375 : Blo 1967435 10786375 := bstep (se 1 (by rfl) ⟨8089781, by rfl⟩ : syracuseStep 10786375 = 16179563) B16179563
theorem B14381833 : Blo 1967435 14381833 := bstep (se 2 (by rfl) ⟨5393187, by rfl⟩ : syracuseStep 14381833 = 10786375) B10786375
theorem B19175777 : Blo 1967435 19175777 := bstep (se 2 (by rfl) ⟨7190916, by rfl⟩ : syracuseStep 19175777 = 14381833) B14381833
theorem B12783851 : Blo 1967435 12783851 := bstep (se 1 (by rfl) ⟨9587888, by rfl⟩ : syracuseStep 12783851 = 19175777) B19175777
theorem B8522567 : Blo 1967435 8522567 := bstep (se 1 (by rfl) ⟨6391925, by rfl⟩ : syracuseStep 8522567 = 12783851) B12783851
theorem B5681711 : Blo 1967435 5681711 := bstep (se 1 (by rfl) ⟨4261283, by rfl⟩ : syracuseStep 5681711 = 8522567) B8522567
theorem B3787807 : Blo 1967435 3787807 := bstep (se 1 (by rfl) ⟨2840855, by rfl⟩ : syracuseStep 3787807 = 5681711) B5681711
theorem B5050409 : Blo 1967435 5050409 := bstep (se 2 (by rfl) ⟨1893903, by rfl⟩ : syracuseStep 5050409 = 3787807) B3787807
theorem B13467757 : Blo 1967435 13467757 := bstep (se 3 (by rfl) ⟨2525204, by rfl⟩ : syracuseStep 13467757 = 5050409) B5050409
theorem B17957009 : Blo 1967435 17957009 := bstep (se 2 (by rfl) ⟨6733878, by rfl⟩ : syracuseStep 17957009 = 13467757) B13467757
theorem B47885357 : Blo 1967435 47885357 := bstep (se 3 (by rfl) ⟨8978504, by rfl⟩ : syracuseStep 47885357 = 17957009) B17957009
theorem B31923571 : Blo 1967435 31923571 := bstep (se 1 (by rfl) ⟨23942678, by rfl⟩ : syracuseStep 31923571 = 47885357) B47885357
theorem B42564761 : Blo 1967435 42564761 := bstep (se 2 (by rfl) ⟨15961785, by rfl⟩ : syracuseStep 42564761 = 31923571) B31923571
theorem B28376507 : Blo 1967435 28376507 := bstep (se 1 (by rfl) ⟨21282380, by rfl⟩ : syracuseStep 28376507 = 42564761) B42564761
theorem B18917671 : Blo 1967435 18917671 := bstep (se 1 (by rfl) ⟨14188253, by rfl⟩ : syracuseStep 18917671 = 28376507) B28376507
theorem B25223561 : Blo 1967435 25223561 := bstep (se 2 (by rfl) ⟨9458835, by rfl⟩ : syracuseStep 25223561 = 18917671) B18917671
theorem B16815707 : Blo 1967435 16815707 := bstep (se 1 (by rfl) ⟨12611780, by rfl⟩ : syracuseStep 16815707 = 25223561) B25223561
theorem B11210471 : Blo 1967435 11210471 := bstep (se 1 (by rfl) ⟨8407853, by rfl⟩ : syracuseStep 11210471 = 16815707) B16815707
theorem B7473647 : Blo 1967435 7473647 := bstep (se 1 (by rfl) ⟨5605235, by rfl⟩ : syracuseStep 7473647 = 11210471) B11210471
theorem B4982431 : Blo 1967435 4982431 := bstep (se 1 (by rfl) ⟨3736823, by rfl⟩ : syracuseStep 4982431 = 7473647) B7473647
theorem B6643241 : Blo 1967435 6643241 := bstep (se 2 (by rfl) ⟨2491215, by rfl⟩ : syracuseStep 6643241 = 4982431) B4982431
theorem B4428827 : Blo 1967435 4428827 := bstep (se 1 (by rfl) ⟨3321620, by rfl⟩ : syracuseStep 4428827 = 6643241) B6643241
theorem B2952551 : Blo 1967435 2952551 := bstep (se 1 (by rfl) ⟨2214413, by rfl⟩ : syracuseStep 2952551 = 4428827) B4428827
theorem B1968367 : Blo 1967435 1968367 := bstep (se 1 (by rfl) ⟨1476275, by rfl⟩ : syracuseStep 1968367 = 2952551) B2952551
theorem B2952557 : Blo 1967435 2952557 := bbase (se 3 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 2952557 = 1107209) (by norm_num)
theorem B1968371 : Blo 1967435 1968371 := bstep (se 1 (by rfl) ⟨1476278, by rfl⟩ : syracuseStep 1968371 = 2952557) B2952557
theorem B4428845 : Blo 1967435 4428845 := bbase (se 3 (by rfl) ⟨830408, by rfl⟩ : syracuseStep 4428845 = 1660817) (by norm_num)
theorem B2952563 : Blo 1967435 2952563 := bstep (se 1 (by rfl) ⟨2214422, by rfl⟩ : syracuseStep 2952563 = 4428845) B4428845
theorem B1968375 : Blo 1967435 1968375 := bstep (se 1 (by rfl) ⟨1476281, by rfl⟩ : syracuseStep 1968375 = 2952563) B2952563
theorem B12611861 : Blo 1967435 12611861 := bbase (se 6 (by rfl) ⟨295590, by rfl⟩ : syracuseStep 12611861 = 591181) (by norm_num)
theorem B8407907 : Blo 1967435 8407907 := bstep (se 1 (by rfl) ⟨6305930, by rfl⟩ : syracuseStep 8407907 = 12611861) B12611861
theorem B5605271 : Blo 1967435 5605271 := bstep (se 1 (by rfl) ⟨4203953, by rfl⟩ : syracuseStep 5605271 = 8407907) B8407907
theorem B3736847 : Blo 1967435 3736847 := bstep (se 1 (by rfl) ⟨2802635, by rfl⟩ : syracuseStep 3736847 = 5605271) B5605271
theorem B2491231 : Blo 1967435 2491231 := bstep (se 1 (by rfl) ⟨1868423, by rfl⟩ : syracuseStep 2491231 = 3736847) B3736847
theorem B3321641 : Blo 1967435 3321641 := bstep (se 2 (by rfl) ⟨1245615, by rfl⟩ : syracuseStep 3321641 = 2491231) B2491231
theorem B2214427 : Blo 1967435 2214427 := bstep (se 1 (by rfl) ⟨1660820, by rfl⟩ : syracuseStep 2214427 = 3321641) B3321641
theorem B2952569 : Blo 1967435 2952569 := bstep (se 2 (by rfl) ⟨1107213, by rfl⟩ : syracuseStep 2952569 = 2214427) B2214427
theorem B1968379 : Blo 1967435 1968379 := bstep (se 1 (by rfl) ⟨1476284, by rfl⟩ : syracuseStep 1968379 = 2952569) B2952569
theorem B6305941 : Blo 1967435 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B33631685 : Blo 1967435 33631685 := bstep (se 4 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 33631685 = 6305941) B6305941
theorem B22421123 : Blo 1967435 22421123 := bstep (se 1 (by rfl) ⟨16815842, by rfl⟩ : syracuseStep 22421123 = 33631685) B33631685
theorem B14947415 : Blo 1967435 14947415 := bstep (se 1 (by rfl) ⟨11210561, by rfl⟩ : syracuseStep 14947415 = 22421123) B22421123
theorem B9964943 : Blo 1967435 9964943 := bstep (se 1 (by rfl) ⟨7473707, by rfl⟩ : syracuseStep 9964943 = 14947415) B14947415
theorem B6643295 : Blo 1967435 6643295 := bstep (se 1 (by rfl) ⟨4982471, by rfl⟩ : syracuseStep 6643295 = 9964943) B9964943
theorem B4428863 : Blo 1967435 4428863 := bstep (se 1 (by rfl) ⟨3321647, by rfl⟩ : syracuseStep 4428863 = 6643295) B6643295
theorem B2952575 : Blo 1967435 2952575 := bstep (se 1 (by rfl) ⟨2214431, by rfl⟩ : syracuseStep 2952575 = 4428863) B4428863
theorem B1968383 : Blo 1967435 1968383 := bstep (se 1 (by rfl) ⟨1476287, by rfl⟩ : syracuseStep 1968383 = 2952575) B2952575
theorem B2952581 : Blo 1967435 2952581 := bbase (se 4 (by rfl) ⟨276804, by rfl⟩ : syracuseStep 2952581 = 553609) (by norm_num)
theorem B1968387 : Blo 1967435 1968387 := bstep (se 1 (by rfl) ⟨1476290, by rfl⟩ : syracuseStep 1968387 = 2952581) B2952581
theorem B3321661 : Blo 1967435 3321661 := bbase (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) (by norm_num)
theorem B4428881 : Blo 1967435 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B2952587 : Blo 1967435 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B1968391 : Blo 1967435 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B2214445 : Blo 1967435 2214445 := bbase (se 3 (by rfl) ⟨415208, by rfl⟩ : syracuseStep 2214445 = 830417) (by norm_num)
theorem B2952593 : Blo 1967435 2952593 := bstep (se 2 (by rfl) ⟨1107222, by rfl⟩ : syracuseStep 2952593 = 2214445) B2214445
theorem B1968395 : Blo 1967435 1968395 := bstep (se 1 (by rfl) ⟨1476296, by rfl⟩ : syracuseStep 1968395 = 2952593) B2952593
theorem B6643349 : Blo 1967435 6643349 := bbase (se 6 (by rfl) ⟨155703, by rfl⟩ : syracuseStep 6643349 = 311407) (by norm_num)
theorem B4428899 : Blo 1967435 4428899 := bstep (se 1 (by rfl) ⟨3321674, by rfl⟩ : syracuseStep 4428899 = 6643349) B6643349
theorem B2952599 : Blo 1967435 2952599 := bstep (se 1 (by rfl) ⟨2214449, by rfl⟩ : syracuseStep 2952599 = 4428899) B4428899
theorem B1968399 : Blo 1967435 1968399 := bstep (se 1 (by rfl) ⟨1476299, by rfl⟩ : syracuseStep 1968399 = 2952599) B2952599
theorem B2952605 : Blo 1967435 2952605 := bbase (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) (by norm_num)
theorem B1968403 : Blo 1967435 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B4428917 : Blo 1967435 4428917 := bbase (se 5 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 4428917 = 415211) (by norm_num)
theorem B2952611 : Blo 1967435 2952611 := bstep (se 1 (by rfl) ⟨2214458, by rfl⟩ : syracuseStep 2952611 = 4428917) B4428917
theorem B1968407 : Blo 1967435 1968407 := bstep (se 1 (by rfl) ⟨1476305, by rfl⟩ : syracuseStep 1968407 = 2952611) B2952611
theorem B16816085 : Blo 1967435 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B11210723 : Blo 1967435 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B7473815 : Blo 1967435 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B4982543 : Blo 1967435 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B3321695 : Blo 1967435 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B2214463 : Blo 1967435 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B2952617 : Blo 1967435 2952617 := bstep (se 2 (by rfl) ⟨1107231, by rfl⟩ : syracuseStep 2952617 = 2214463) B2214463
theorem B1968411 : Blo 1967435 1968411 := bstep (se 1 (by rfl) ⟨1476308, by rfl⟩ : syracuseStep 1968411 = 2952617) B2952617
theorem B7473829 : Blo 1967435 7473829 := bbase (se 4 (by rfl) ⟨700671, by rfl⟩ : syracuseStep 7473829 = 1401343) (by norm_num)
theorem B9965105 : Blo 1967435 9965105 := bstep (se 2 (by rfl) ⟨3736914, by rfl⟩ : syracuseStep 9965105 = 7473829) B7473829
theorem B6643403 : Blo 1967435 6643403 := bstep (se 1 (by rfl) ⟨4982552, by rfl⟩ : syracuseStep 6643403 = 9965105) B9965105
theorem B4428935 : Blo 1967435 4428935 := bstep (se 1 (by rfl) ⟨3321701, by rfl⟩ : syracuseStep 4428935 = 6643403) B6643403
theorem B2952623 : Blo 1967435 2952623 := bstep (se 1 (by rfl) ⟨2214467, by rfl⟩ : syracuseStep 2952623 = 4428935) B4428935
theorem B1968415 : Blo 1967435 1968415 := bstep (se 1 (by rfl) ⟨1476311, by rfl⟩ : syracuseStep 1968415 = 2952623) B2952623
theorem B2952629 : Blo 1967435 2952629 := bbase (se 5 (by rfl) ⟨138404, by rfl⟩ : syracuseStep 2952629 = 276809) (by norm_num)
theorem B1968419 : Blo 1967435 1968419 := bstep (se 1 (by rfl) ⟨1476314, by rfl⟩ : syracuseStep 1968419 = 2952629) B2952629
theorem B4982573 : Blo 1967435 4982573 := bbase (se 3 (by rfl) ⟨934232, by rfl⟩ : syracuseStep 4982573 = 1868465) (by norm_num)
theorem B3321715 : Blo 1967435 3321715 := bstep (se 1 (by rfl) ⟨2491286, by rfl⟩ : syracuseStep 3321715 = 4982573) B4982573
theorem B4428953 : Blo 1967435 4428953 := bstep (se 2 (by rfl) ⟨1660857, by rfl⟩ : syracuseStep 4428953 = 3321715) B3321715
theorem B2952635 : Blo 1967435 2952635 := bstep (se 1 (by rfl) ⟨2214476, by rfl⟩ : syracuseStep 2952635 = 4428953) B4428953
theorem B1968423 : Blo 1967435 1968423 := bstep (se 1 (by rfl) ⟨1476317, by rfl⟩ : syracuseStep 1968423 = 2952635) B2952635
theorem B2214481 : Blo 1967435 2214481 := bbase (se 2 (by rfl) ⟨830430, by rfl⟩ : syracuseStep 2214481 = 1660861) (by norm_num)
theorem B2952641 : Blo 1967435 2952641 := bstep (se 2 (by rfl) ⟨1107240, by rfl⟩ : syracuseStep 2952641 = 2214481) B2214481
theorem B1968427 : Blo 1967435 1968427 := bstep (se 1 (by rfl) ⟨1476320, by rfl⟩ : syracuseStep 1968427 = 2952641) B2952641
theorem B2802709 : Blo 1967435 2802709 := bbase (se 6 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 2802709 = 131377) (by norm_num)
theorem B3736945 : Blo 1967435 3736945 := bstep (se 2 (by rfl) ⟨1401354, by rfl⟩ : syracuseStep 3736945 = 2802709) B2802709
theorem B4982593 : Blo 1967435 4982593 := bstep (se 2 (by rfl) ⟨1868472, by rfl⟩ : syracuseStep 4982593 = 3736945) B3736945
theorem B6643457 : Blo 1967435 6643457 := bstep (se 2 (by rfl) ⟨2491296, by rfl⟩ : syracuseStep 6643457 = 4982593) B4982593
theorem B4428971 : Blo 1967435 4428971 := bstep (se 1 (by rfl) ⟨3321728, by rfl⟩ : syracuseStep 4428971 = 6643457) B6643457
theorem B2952647 : Blo 1967435 2952647 := bstep (se 1 (by rfl) ⟨2214485, by rfl⟩ : syracuseStep 2952647 = 4428971) B4428971
theorem B1968431 : Blo 1967435 1968431 := bstep (se 1 (by rfl) ⟨1476323, by rfl⟩ : syracuseStep 1968431 = 2952647) B2952647
theorem B2952653 : Blo 1967435 2952653 := bbase (se 3 (by rfl) ⟨553622, by rfl⟩ : syracuseStep 2952653 = 1107245) (by norm_num)
theorem B1968435 : Blo 1967435 1968435 := bstep (se 1 (by rfl) ⟨1476326, by rfl⟩ : syracuseStep 1968435 = 2952653) B2952653
theorem B4428989 : Blo 1967435 4428989 := bbase (se 3 (by rfl) ⟨830435, by rfl⟩ : syracuseStep 4428989 = 1660871) (by norm_num)
theorem B2952659 : Blo 1967435 2952659 := bstep (se 1 (by rfl) ⟨2214494, by rfl⟩ : syracuseStep 2952659 = 4428989) B4428989
theorem B1968439 : Blo 1967435 1968439 := bstep (se 1 (by rfl) ⟨1476329, by rfl⟩ : syracuseStep 1968439 = 2952659) B2952659
theorem B3321749 : Blo 1967435 3321749 := bbase (se 6 (by rfl) ⟨77853, by rfl⟩ : syracuseStep 3321749 = 155707) (by norm_num)
theorem B2214499 : Blo 1967435 2214499 := bstep (se 1 (by rfl) ⟨1660874, by rfl⟩ : syracuseStep 2214499 = 3321749) B3321749
theorem B2952665 : Blo 1967435 2952665 := bstep (se 2 (by rfl) ⟨1107249, by rfl⟩ : syracuseStep 2952665 = 2214499) B2214499
theorem B1968443 : Blo 1967435 1968443 := bstep (se 1 (by rfl) ⟨1476332, by rfl⟩ : syracuseStep 1968443 = 2952665) B2952665
theorem B2364805 : Blo 1967435 2364805 := bbase (se 4 (by rfl) ⟨221700, by rfl⟩ : syracuseStep 2364805 = 443401) (by norm_num)
theorem B12612293 : Blo 1967435 12612293 := bstep (se 4 (by rfl) ⟨1182402, by rfl⟩ : syracuseStep 12612293 = 2364805) B2364805
theorem B8408195 : Blo 1967435 8408195 := bstep (se 1 (by rfl) ⟨6306146, by rfl⟩ : syracuseStep 8408195 = 12612293) B12612293
theorem B5605463 : Blo 1967435 5605463 := bstep (se 1 (by rfl) ⟨4204097, by rfl⟩ : syracuseStep 5605463 = 8408195) B8408195
theorem B14947901 : Blo 1967435 14947901 := bstep (se 3 (by rfl) ⟨2802731, by rfl⟩ : syracuseStep 14947901 = 5605463) B5605463
theorem B9965267 : Blo 1967435 9965267 := bstep (se 1 (by rfl) ⟨7473950, by rfl⟩ : syracuseStep 9965267 = 14947901) B14947901
theorem B6643511 : Blo 1967435 6643511 := bstep (se 1 (by rfl) ⟨4982633, by rfl⟩ : syracuseStep 6643511 = 9965267) B9965267
theorem B4429007 : Blo 1967435 4429007 := bstep (se 1 (by rfl) ⟨3321755, by rfl⟩ : syracuseStep 4429007 = 6643511) B6643511
theorem B2952671 : Blo 1967435 2952671 := bstep (se 1 (by rfl) ⟨2214503, by rfl⟩ : syracuseStep 2952671 = 4429007) B4429007
theorem B1968447 : Blo 1967435 1968447 := bstep (se 1 (by rfl) ⟨1476335, by rfl⟩ : syracuseStep 1968447 = 2952671) B2952671
theorem B2952677 : Blo 1967435 2952677 := bbase (se 4 (by rfl) ⟨276813, by rfl⟩ : syracuseStep 2952677 = 553627) (by norm_num)
theorem B1968451 : Blo 1967435 1968451 := bstep (se 1 (by rfl) ⟨1476338, by rfl⟩ : syracuseStep 1968451 = 2952677) B2952677
theorem B26936725 : Blo 1967435 26936725 := bbase (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) (by norm_num)
theorem B35915633 : Blo 1967435 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B23943755 : Blo 1967435 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B15962503 : Blo 1967435 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B21283337 : Blo 1967435 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B14188891 : Blo 1967435 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B18918521 : Blo 1967435 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B12612347 : Blo 1967435 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B8408231 : Blo 1967435 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B5605487 : Blo 1967435 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B3736991 : Blo 1967435 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B2491327 : Blo 1967435 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B3321769 : Blo 1967435 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B4429025 : Blo 1967435 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B2952683 : Blo 1967435 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B1968455 : Blo 1967435 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B2214517 : Blo 1967435 2214517 := bbase (se 5 (by rfl) ⟨103805, by rfl⟩ : syracuseStep 2214517 = 207611) (by norm_num)
theorem B2952689 : Blo 1967435 2952689 := bstep (se 2 (by rfl) ⟨1107258, by rfl⟩ : syracuseStep 2952689 = 2214517) B2214517
theorem B1968459 : Blo 1967435 1968459 := bstep (se 1 (by rfl) ⟨1476344, by rfl⟩ : syracuseStep 1968459 = 2952689) B2952689
theorem B2491337 : Blo 1967435 2491337 := bbase (se 2 (by rfl) ⟨934251, by rfl⟩ : syracuseStep 2491337 = 1868503) (by norm_num)
theorem B6643565 : Blo 1967435 6643565 := bstep (se 3 (by rfl) ⟨1245668, by rfl⟩ : syracuseStep 6643565 = 2491337) B2491337
theorem B4429043 : Blo 1967435 4429043 := bstep (se 1 (by rfl) ⟨3321782, by rfl⟩ : syracuseStep 4429043 = 6643565) B6643565
theorem B2952695 : Blo 1967435 2952695 := bstep (se 1 (by rfl) ⟨2214521, by rfl⟩ : syracuseStep 2952695 = 4429043) B4429043
theorem B1968463 : Blo 1967435 1968463 := bstep (se 1 (by rfl) ⟨1476347, by rfl⟩ : syracuseStep 1968463 = 2952695) B2952695
theorem B2952701 : Blo 1967435 2952701 := bbase (se 3 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 2952701 = 1107263) (by norm_num)
theorem B1968467 : Blo 1967435 1968467 := bstep (se 1 (by rfl) ⟨1476350, by rfl⟩ : syracuseStep 1968467 = 2952701) B2952701
theorem B4429061 : Blo 1967435 4429061 := bbase (se 4 (by rfl) ⟨415224, by rfl⟩ : syracuseStep 4429061 = 830449) (by norm_num)
theorem B2952707 : Blo 1967435 2952707 := bstep (se 1 (by rfl) ⟨2214530, by rfl⟩ : syracuseStep 2952707 = 4429061) B4429061
theorem B1968471 : Blo 1967435 1968471 := bstep (se 1 (by rfl) ⟨1476353, by rfl⟩ : syracuseStep 1968471 = 2952707) B2952707
theorem B3737029 : Blo 1967435 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B4982705 : Blo 1967435 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B3321803 : Blo 1967435 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B2214535 : Blo 1967435 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B2952713 : Blo 1967435 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B1968475 : Blo 1967435 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B9965429 : Blo 1967435 9965429 := bbase (se 5 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 9965429 = 934259) (by norm_num)
theorem B6643619 : Blo 1967435 6643619 := bstep (se 1 (by rfl) ⟨4982714, by rfl⟩ : syracuseStep 6643619 = 9965429) B9965429
theorem B4429079 : Blo 1967435 4429079 := bstep (se 1 (by rfl) ⟨3321809, by rfl⟩ : syracuseStep 4429079 = 6643619) B6643619
theorem B2952719 : Blo 1967435 2952719 := bstep (se 1 (by rfl) ⟨2214539, by rfl⟩ : syracuseStep 2952719 = 4429079) B4429079
theorem B1968479 : Blo 1967435 1968479 := bstep (se 1 (by rfl) ⟨1476359, by rfl⟩ : syracuseStep 1968479 = 2952719) B2952719
theorem B2952725 : Blo 1967435 2952725 := bbase (se 6 (by rfl) ⟨69204, by rfl⟩ : syracuseStep 2952725 = 138409) (by norm_num)
theorem B1968483 : Blo 1967435 1968483 := bstep (se 1 (by rfl) ⟨1476362, by rfl⟩ : syracuseStep 1968483 = 2952725) B2952725
theorem B9459413 : Blo 1967435 9459413 := bbase (se 7 (by rfl) ⟨110852, by rfl⟩ : syracuseStep 9459413 = 221705) (by norm_num)
theorem B6306275 : Blo 1967435 6306275 := bstep (se 1 (by rfl) ⟨4729706, by rfl⟩ : syracuseStep 6306275 = 9459413) B9459413
theorem B16816733 : Blo 1967435 16816733 := bstep (se 3 (by rfl) ⟨3153137, by rfl⟩ : syracuseStep 16816733 = 6306275) B6306275
theorem B11211155 : Blo 1967435 11211155 := bstep (se 1 (by rfl) ⟨8408366, by rfl⟩ : syracuseStep 11211155 = 16816733) B16816733
theorem B7474103 : Blo 1967435 7474103 := bstep (se 1 (by rfl) ⟨5605577, by rfl⟩ : syracuseStep 7474103 = 11211155) B11211155
theorem B4982735 : Blo 1967435 4982735 := bstep (se 1 (by rfl) ⟨3737051, by rfl⟩ : syracuseStep 4982735 = 7474103) B7474103
theorem B3321823 : Blo 1967435 3321823 := bstep (se 1 (by rfl) ⟨2491367, by rfl⟩ : syracuseStep 3321823 = 4982735) B4982735
theorem B4429097 : Blo 1967435 4429097 := bstep (se 2 (by rfl) ⟨1660911, by rfl⟩ : syracuseStep 4429097 = 3321823) B3321823
theorem B2952731 : Blo 1967435 2952731 := bstep (se 1 (by rfl) ⟨2214548, by rfl⟩ : syracuseStep 2952731 = 4429097) B4429097
theorem B1968487 : Blo 1967435 1968487 := bstep (se 1 (by rfl) ⟨1476365, by rfl⟩ : syracuseStep 1968487 = 2952731) B2952731
theorem B2214553 : Blo 1967435 2214553 := bbase (se 2 (by rfl) ⟨830457, by rfl⟩ : syracuseStep 2214553 = 1660915) (by norm_num)
theorem B2952737 : Blo 1967435 2952737 := bstep (se 2 (by rfl) ⟨1107276, by rfl⟩ : syracuseStep 2952737 = 2214553) B2214553
theorem B1968491 : Blo 1967435 1968491 := bstep (se 1 (by rfl) ⟨1476368, by rfl⟩ : syracuseStep 1968491 = 2952737) B2952737
theorem B7474133 : Blo 1967435 7474133 := bbase (se 7 (by rfl) ⟨87587, by rfl⟩ : syracuseStep 7474133 = 175175) (by norm_num)
theorem B4982755 : Blo 1967435 4982755 := bstep (se 1 (by rfl) ⟨3737066, by rfl⟩ : syracuseStep 4982755 = 7474133) B7474133
theorem B6643673 : Blo 1967435 6643673 := bstep (se 2 (by rfl) ⟨2491377, by rfl⟩ : syracuseStep 6643673 = 4982755) B4982755
theorem B4429115 : Blo 1967435 4429115 := bstep (se 1 (by rfl) ⟨3321836, by rfl⟩ : syracuseStep 4429115 = 6643673) B6643673
theorem B2952743 : Blo 1967435 2952743 := bstep (se 1 (by rfl) ⟨2214557, by rfl⟩ : syracuseStep 2952743 = 4429115) B4429115
theorem B1968495 : Blo 1967435 1968495 := bstep (se 1 (by rfl) ⟨1476371, by rfl⟩ : syracuseStep 1968495 = 2952743) B2952743
theorem B2952749 : Blo 1967435 2952749 := bbase (se 3 (by rfl) ⟨553640, by rfl⟩ : syracuseStep 2952749 = 1107281) (by norm_num)
theorem B1968499 : Blo 1967435 1968499 := bstep (se 1 (by rfl) ⟨1476374, by rfl⟩ : syracuseStep 1968499 = 2952749) B2952749
theorem B4429133 : Blo 1967435 4429133 := bbase (se 3 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 4429133 = 1660925) (by norm_num)
theorem B2952755 : Blo 1967435 2952755 := bstep (se 1 (by rfl) ⟨2214566, by rfl⟩ : syracuseStep 2952755 = 4429133) B4429133
theorem B1968503 : Blo 1967435 1968503 := bstep (se 1 (by rfl) ⟨1476377, by rfl⟩ : syracuseStep 1968503 = 2952755) B2952755
theorem B2491393 : Blo 1967435 2491393 := bbase (se 2 (by rfl) ⟨934272, by rfl⟩ : syracuseStep 2491393 = 1868545) (by norm_num)
theorem B3321857 : Blo 1967435 3321857 := bstep (se 2 (by rfl) ⟨1245696, by rfl⟩ : syracuseStep 3321857 = 2491393) B2491393
theorem B2214571 : Blo 1967435 2214571 := bstep (se 1 (by rfl) ⟨1660928, by rfl⟩ : syracuseStep 2214571 = 3321857) B3321857
theorem B2952761 : Blo 1967435 2952761 := bstep (se 2 (by rfl) ⟨1107285, by rfl⟩ : syracuseStep 2952761 = 2214571) B2214571
theorem B1968507 : Blo 1967435 1968507 := bstep (se 1 (by rfl) ⟨1476380, by rfl⟩ : syracuseStep 1968507 = 2952761) B2952761
theorem B2102117 : Blo 1967435 2102117 := bbase (se 4 (by rfl) ⟨197073, by rfl⟩ : syracuseStep 2102117 = 394147) (by norm_num)
theorem B22422581 : Blo 1967435 22422581 := bstep (se 5 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 22422581 = 2102117) B2102117
theorem B14948387 : Blo 1967435 14948387 := bstep (se 1 (by rfl) ⟨11211290, by rfl⟩ : syracuseStep 14948387 = 22422581) B22422581
theorem B9965591 : Blo 1967435 9965591 := bstep (se 1 (by rfl) ⟨7474193, by rfl⟩ : syracuseStep 9965591 = 14948387) B14948387
theorem B6643727 : Blo 1967435 6643727 := bstep (se 1 (by rfl) ⟨4982795, by rfl⟩ : syracuseStep 6643727 = 9965591) B9965591
theorem B4429151 : Blo 1967435 4429151 := bstep (se 1 (by rfl) ⟨3321863, by rfl⟩ : syracuseStep 4429151 = 6643727) B6643727
theorem B2952767 : Blo 1967435 2952767 := bstep (se 1 (by rfl) ⟨2214575, by rfl⟩ : syracuseStep 2952767 = 4429151) B4429151
theorem B1968511 : Blo 1967435 1968511 := bstep (se 1 (by rfl) ⟨1476383, by rfl⟩ : syracuseStep 1968511 = 2952767) B2952767
theorem B2952773 : Blo 1967435 2952773 := bbase (se 4 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 2952773 = 553645) (by norm_num)
theorem B1968515 : Blo 1967435 1968515 := bstep (se 1 (by rfl) ⟨1476386, by rfl⟩ : syracuseStep 1968515 = 2952773) B2952773
theorem B3321877 : Blo 1967435 3321877 := bbase (se 6 (by rfl) ⟨77856, by rfl⟩ : syracuseStep 3321877 = 155713) (by norm_num)
theorem B4429169 : Blo 1967435 4429169 := bstep (se 2 (by rfl) ⟨1660938, by rfl⟩ : syracuseStep 4429169 = 3321877) B3321877
theorem B2952779 : Blo 1967435 2952779 := bstep (se 1 (by rfl) ⟨2214584, by rfl⟩ : syracuseStep 2952779 = 4429169) B4429169
theorem B1968519 : Blo 1967435 1968519 := bstep (se 1 (by rfl) ⟨1476389, by rfl⟩ : syracuseStep 1968519 = 2952779) B2952779
theorem B2214589 : Blo 1967435 2214589 := bbase (se 3 (by rfl) ⟨415235, by rfl⟩ : syracuseStep 2214589 = 830471) (by norm_num)
theorem B2952785 : Blo 1967435 2952785 := bstep (se 2 (by rfl) ⟨1107294, by rfl⟩ : syracuseStep 2952785 = 2214589) B2214589
theorem B1968523 : Blo 1967435 1968523 := bstep (se 1 (by rfl) ⟨1476392, by rfl⟩ : syracuseStep 1968523 = 2952785) B2952785
theorem B6643781 : Blo 1967435 6643781 := bbase (se 4 (by rfl) ⟨622854, by rfl⟩ : syracuseStep 6643781 = 1245709) (by norm_num)
theorem B4429187 : Blo 1967435 4429187 := bstep (se 1 (by rfl) ⟨3321890, by rfl⟩ : syracuseStep 4429187 = 6643781) B6643781
theorem B2952791 : Blo 1967435 2952791 := bstep (se 1 (by rfl) ⟨2214593, by rfl⟩ : syracuseStep 2952791 = 4429187) B4429187
theorem B1968527 : Blo 1967435 1968527 := bstep (se 1 (by rfl) ⟨1476395, by rfl⟩ : syracuseStep 1968527 = 2952791) B2952791
theorem B2952797 : Blo 1967435 2952797 := bbase (se 3 (by rfl) ⟨553649, by rfl⟩ : syracuseStep 2952797 = 1107299) (by norm_num)
theorem B1968531 : Blo 1967435 1968531 := bstep (se 1 (by rfl) ⟨1476398, by rfl⟩ : syracuseStep 1968531 = 2952797) B2952797
theorem B4429205 : Blo 1967435 4429205 := bbase (se 6 (by rfl) ⟨103809, by rfl⟩ : syracuseStep 4429205 = 207619) (by norm_num)
theorem B2952803 : Blo 1967435 2952803 := bstep (se 1 (by rfl) ⟨2214602, by rfl⟩ : syracuseStep 2952803 = 4429205) B4429205
theorem B1968535 : Blo 1967435 1968535 := bstep (se 1 (by rfl) ⟨1476401, by rfl⟩ : syracuseStep 1968535 = 2952803) B2952803
theorem B3990797 : Blo 1967435 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2660531 : Blo 1967435 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B7094749 : Blo 1967435 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B9459665 : Blo 1967435 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6306443 : Blo 1967435 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B4204295 : Blo 1967435 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2802863 : Blo 1967435 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B7474301 : Blo 1967435 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B4982867 : Blo 1967435 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B3321911 : Blo 1967435 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B2214607 : Blo 1967435 2214607 := bstep (se 1 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 2214607 = 3321911) B3321911
theorem B2952809 : Blo 1967435 2952809 := bstep (se 2 (by rfl) ⟨1107303, by rfl⟩ : syracuseStep 2952809 = 2214607) B2214607
theorem B1968539 : Blo 1967435 1968539 := bstep (se 1 (by rfl) ⟨1476404, by rfl⟩ : syracuseStep 1968539 = 2952809) B2952809
theorem B3547381 : Blo 1967435 3547381 := bbase (se 5 (by rfl) ⟨166283, by rfl⟩ : syracuseStep 3547381 = 332567) (by norm_num)
theorem B4729841 : Blo 1967435 4729841 := bstep (se 2 (by rfl) ⟨1773690, by rfl⟩ : syracuseStep 4729841 = 3547381) B3547381
theorem B3153227 : Blo 1967435 3153227 := bstep (se 1 (by rfl) ⟨2364920, by rfl⟩ : syracuseStep 3153227 = 4729841) B4729841
theorem B8408605 : Blo 1967435 8408605 := bstep (se 3 (by rfl) ⟨1576613, by rfl⟩ : syracuseStep 8408605 = 3153227) B3153227
theorem B11211473 : Blo 1967435 11211473 := bstep (se 2 (by rfl) ⟨4204302, by rfl⟩ : syracuseStep 11211473 = 8408605) B8408605
theorem B7474315 : Blo 1967435 7474315 := bstep (se 1 (by rfl) ⟨5605736, by rfl⟩ : syracuseStep 7474315 = 11211473) B11211473
theorem B9965753 : Blo 1967435 9965753 := bstep (se 2 (by rfl) ⟨3737157, by rfl⟩ : syracuseStep 9965753 = 7474315) B7474315
theorem B6643835 : Blo 1967435 6643835 := bstep (se 1 (by rfl) ⟨4982876, by rfl⟩ : syracuseStep 6643835 = 9965753) B9965753
theorem B4429223 : Blo 1967435 4429223 := bstep (se 1 (by rfl) ⟨3321917, by rfl⟩ : syracuseStep 4429223 = 6643835) B6643835
theorem B2952815 : Blo 1967435 2952815 := bstep (se 1 (by rfl) ⟨2214611, by rfl⟩ : syracuseStep 2952815 = 4429223) B4429223
theorem B1968543 : Blo 1967435 1968543 := bstep (se 1 (by rfl) ⟨1476407, by rfl⟩ : syracuseStep 1968543 = 2952815) B2952815
theorem B2952821 : Blo 1967435 2952821 := bbase (se 5 (by rfl) ⟨138413, by rfl⟩ : syracuseStep 2952821 = 276827) (by norm_num)
theorem B1968547 : Blo 1967435 1968547 := bstep (se 1 (by rfl) ⟨1476410, by rfl⟩ : syracuseStep 1968547 = 2952821) B2952821
theorem B3737173 : Blo 1967435 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B4982897 : Blo 1967435 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B3321931 : Blo 1967435 3321931 := bstep (se 1 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 3321931 = 4982897) B4982897
theorem B4429241 : Blo 1967435 4429241 := bstep (se 2 (by rfl) ⟨1660965, by rfl⟩ : syracuseStep 4429241 = 3321931) B3321931
theorem B2952827 : Blo 1967435 2952827 := bstep (se 1 (by rfl) ⟨2214620, by rfl⟩ : syracuseStep 2952827 = 4429241) B4429241
theorem B1968551 : Blo 1967435 1968551 := bstep (se 1 (by rfl) ⟨1476413, by rfl⟩ : syracuseStep 1968551 = 2952827) B2952827
theorem B2214625 : Blo 1967435 2214625 := bbase (se 2 (by rfl) ⟨830484, by rfl⟩ : syracuseStep 2214625 = 1660969) (by norm_num)
theorem B2952833 : Blo 1967435 2952833 := bstep (se 2 (by rfl) ⟨1107312, by rfl⟩ : syracuseStep 2952833 = 2214625) B2214625
theorem B1968555 : Blo 1967435 1968555 := bstep (se 1 (by rfl) ⟨1476416, by rfl⟩ : syracuseStep 1968555 = 2952833) B2952833
theorem B4982917 : Blo 1967435 4982917 := bbase (se 4 (by rfl) ⟨467148, by rfl⟩ : syracuseStep 4982917 = 934297) (by norm_num)
theorem B6643889 : Blo 1967435 6643889 := bstep (se 2 (by rfl) ⟨2491458, by rfl⟩ : syracuseStep 6643889 = 4982917) B4982917
theorem B4429259 : Blo 1967435 4429259 := bstep (se 1 (by rfl) ⟨3321944, by rfl⟩ : syracuseStep 4429259 = 6643889) B6643889
theorem B2952839 : Blo 1967435 2952839 := bstep (se 1 (by rfl) ⟨2214629, by rfl⟩ : syracuseStep 2952839 = 4429259) B4429259
theorem B1968559 : Blo 1967435 1968559 := bstep (se 1 (by rfl) ⟨1476419, by rfl⟩ : syracuseStep 1968559 = 2952839) B2952839
theorem B2952845 : Blo 1967435 2952845 := bbase (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) (by norm_num)
theorem B1968563 : Blo 1967435 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B4429277 : Blo 1967435 4429277 := bbase (se 3 (by rfl) ⟨830489, by rfl⟩ : syracuseStep 4429277 = 1660979) (by norm_num)
theorem B2952851 : Blo 1967435 2952851 := bstep (se 1 (by rfl) ⟨2214638, by rfl⟩ : syracuseStep 2952851 = 4429277) B4429277
theorem B1968567 : Blo 1967435 1968567 := bstep (se 1 (by rfl) ⟨1476425, by rfl⟩ : syracuseStep 1968567 = 2952851) B2952851
theorem B3321965 : Blo 1967435 3321965 := bbase (se 3 (by rfl) ⟨622868, by rfl⟩ : syracuseStep 3321965 = 1245737) (by norm_num)
theorem B2214643 : Blo 1967435 2214643 := bstep (se 1 (by rfl) ⟨1660982, by rfl⟩ : syracuseStep 2214643 = 3321965) B3321965
theorem B2952857 : Blo 1967435 2952857 := bstep (se 2 (by rfl) ⟨1107321, by rfl⟩ : syracuseStep 2952857 = 2214643) B2214643
theorem B1968571 : Blo 1967435 1968571 := bstep (se 1 (by rfl) ⟨1476428, by rfl⟩ : syracuseStep 1968571 = 2952857) B2952857
theorem B18919669 : Blo 1967435 18919669 := bbase (se 5 (by rfl) ⟨886859, by rfl⟩ : syracuseStep 18919669 = 1773719) (by norm_num)
theorem B25226225 : Blo 1967435 25226225 := bstep (se 2 (by rfl) ⟨9459834, by rfl⟩ : syracuseStep 25226225 = 18919669) B18919669
theorem B16817483 : Blo 1967435 16817483 := bstep (se 1 (by rfl) ⟨12613112, by rfl⟩ : syracuseStep 16817483 = 25226225) B25226225
theorem B11211655 : Blo 1967435 11211655 := bstep (se 1 (by rfl) ⟨8408741, by rfl⟩ : syracuseStep 11211655 = 16817483) B16817483
theorem B14948873 : Blo 1967435 14948873 := bstep (se 2 (by rfl) ⟨5605827, by rfl⟩ : syracuseStep 14948873 = 11211655) B11211655
theorem B9965915 : Blo 1967435 9965915 := bstep (se 1 (by rfl) ⟨7474436, by rfl⟩ : syracuseStep 9965915 = 14948873) B14948873
theorem B6643943 : Blo 1967435 6643943 := bstep (se 1 (by rfl) ⟨4982957, by rfl⟩ : syracuseStep 6643943 = 9965915) B9965915
theorem B4429295 : Blo 1967435 4429295 := bstep (se 1 (by rfl) ⟨3321971, by rfl⟩ : syracuseStep 4429295 = 6643943) B6643943
theorem B2952863 : Blo 1967435 2952863 := bstep (se 1 (by rfl) ⟨2214647, by rfl⟩ : syracuseStep 2952863 = 4429295) B4429295
theorem B1968575 : Blo 1967435 1968575 := bstep (se 1 (by rfl) ⟨1476431, by rfl⟩ : syracuseStep 1968575 = 2952863) B2952863
theorem B2952869 : Blo 1967435 2952869 := bbase (se 4 (by rfl) ⟨276831, by rfl⟩ : syracuseStep 2952869 = 553663) (by norm_num)
theorem B1968579 : Blo 1967435 1968579 := bstep (se 1 (by rfl) ⟨1476434, by rfl⟩ : syracuseStep 1968579 = 2952869) B2952869
theorem B2491489 : Blo 1967435 2491489 := bbase (se 2 (by rfl) ⟨934308, by rfl⟩ : syracuseStep 2491489 = 1868617) (by norm_num)
theorem B3321985 : Blo 1967435 3321985 := bstep (se 2 (by rfl) ⟨1245744, by rfl⟩ : syracuseStep 3321985 = 2491489) B2491489
theorem B4429313 : Blo 1967435 4429313 := bstep (se 2 (by rfl) ⟨1660992, by rfl⟩ : syracuseStep 4429313 = 3321985) B3321985
theorem B2952875 : Blo 1967435 2952875 := bstep (se 1 (by rfl) ⟨2214656, by rfl⟩ : syracuseStep 2952875 = 4429313) B4429313
theorem B1968583 : Blo 1967435 1968583 := bstep (se 1 (by rfl) ⟨1476437, by rfl⟩ : syracuseStep 1968583 = 2952875) B2952875
theorem B2214661 : Blo 1967435 2214661 := bbase (se 4 (by rfl) ⟨207624, by rfl⟩ : syracuseStep 2214661 = 415249) (by norm_num)
theorem B2952881 : Blo 1967435 2952881 := bstep (se 2 (by rfl) ⟨1107330, by rfl⟩ : syracuseStep 2952881 = 2214661) B2214661
theorem B1968587 : Blo 1967435 1968587 := bstep (se 1 (by rfl) ⟨1476440, by rfl⟩ : syracuseStep 1968587 = 2952881) B2952881
theorem B3547469 : Blo 1967435 3547469 := bbase (se 3 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 3547469 = 1330301) (by norm_num)
theorem B2364979 : Blo 1967435 2364979 := bstep (se 1 (by rfl) ⟨1773734, by rfl⟩ : syracuseStep 2364979 = 3547469) B3547469
theorem B3153305 : Blo 1967435 3153305 := bstep (se 2 (by rfl) ⟨1182489, by rfl⟩ : syracuseStep 3153305 = 2364979) B2364979
theorem B2102203 : Blo 1967435 2102203 := bstep (se 1 (by rfl) ⟨1576652, by rfl⟩ : syracuseStep 2102203 = 3153305) B3153305
theorem B2802937 : Blo 1967435 2802937 := bstep (se 2 (by rfl) ⟨1051101, by rfl⟩ : syracuseStep 2802937 = 2102203) B2102203
theorem B3737249 : Blo 1967435 3737249 := bstep (se 2 (by rfl) ⟨1401468, by rfl⟩ : syracuseStep 3737249 = 2802937) B2802937
theorem B2491499 : Blo 1967435 2491499 := bstep (se 1 (by rfl) ⟨1868624, by rfl⟩ : syracuseStep 2491499 = 3737249) B3737249
theorem B6643997 : Blo 1967435 6643997 := bstep (se 3 (by rfl) ⟨1245749, by rfl⟩ : syracuseStep 6643997 = 2491499) B2491499
theorem B4429331 : Blo 1967435 4429331 := bstep (se 1 (by rfl) ⟨3321998, by rfl⟩ : syracuseStep 4429331 = 6643997) B6643997
theorem B2952887 : Blo 1967435 2952887 := bstep (se 1 (by rfl) ⟨2214665, by rfl⟩ : syracuseStep 2952887 = 4429331) B4429331
theorem B1968591 : Blo 1967435 1968591 := bstep (se 1 (by rfl) ⟨1476443, by rfl⟩ : syracuseStep 1968591 = 2952887) B2952887
theorem B2952893 : Blo 1967435 2952893 := bbase (se 3 (by rfl) ⟨553667, by rfl⟩ : syracuseStep 2952893 = 1107335) (by norm_num)
theorem B1968595 : Blo 1967435 1968595 := bstep (se 1 (by rfl) ⟨1476446, by rfl⟩ : syracuseStep 1968595 = 2952893) B2952893
theorem B4429349 : Blo 1967435 4429349 := bbase (se 4 (by rfl) ⟨415251, by rfl⟩ : syracuseStep 4429349 = 830503) (by norm_num)
theorem B2952899 : Blo 1967435 2952899 := bstep (se 1 (by rfl) ⟨2214674, by rfl⟩ : syracuseStep 2952899 = 4429349) B4429349
theorem B1968599 : Blo 1967435 1968599 := bstep (se 1 (by rfl) ⟨1476449, by rfl⟩ : syracuseStep 1968599 = 2952899) B2952899
theorem B4983029 : Blo 1967435 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B3322019 : Blo 1967435 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B2214679 : Blo 1967435 2214679 := bstep (se 1 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 2214679 = 3322019) B3322019
theorem B2952905 : Blo 1967435 2952905 := bstep (se 2 (by rfl) ⟨1107339, by rfl⟩ : syracuseStep 2952905 = 2214679) B2214679
theorem B1968603 : Blo 1967435 1968603 := bstep (se 1 (by rfl) ⟨1476452, by rfl⟩ : syracuseStep 1968603 = 2952905) B2952905
theorem B15963733 : Blo 1967435 15963733 := bbase (se 8 (by rfl) ⟨93537, by rfl⟩ : syracuseStep 15963733 = 187075) (by norm_num)
theorem B21284977 : Blo 1967435 21284977 := bstep (se 2 (by rfl) ⟨7981866, by rfl⟩ : syracuseStep 21284977 = 15963733) B15963733
theorem B28379969 : Blo 1967435 28379969 := bstep (se 2 (by rfl) ⟨10642488, by rfl⟩ : syracuseStep 28379969 = 21284977) B21284977
theorem B18919979 : Blo 1967435 18919979 := bstep (se 1 (by rfl) ⟨14189984, by rfl⟩ : syracuseStep 18919979 = 28379969) B28379969
theorem B12613319 : Blo 1967435 12613319 := bstep (se 1 (by rfl) ⟨9459989, by rfl⟩ : syracuseStep 12613319 = 18919979) B18919979
theorem B8408879 : Blo 1967435 8408879 := bstep (se 1 (by rfl) ⟨6306659, by rfl⟩ : syracuseStep 8408879 = 12613319) B12613319
theorem B5605919 : Blo 1967435 5605919 := bstep (se 1 (by rfl) ⟨4204439, by rfl⟩ : syracuseStep 5605919 = 8408879) B8408879
theorem B3737279 : Blo 1967435 3737279 := bstep (se 1 (by rfl) ⟨2802959, by rfl⟩ : syracuseStep 3737279 = 5605919) B5605919
theorem B9966077 : Blo 1967435 9966077 := bstep (se 3 (by rfl) ⟨1868639, by rfl⟩ : syracuseStep 9966077 = 3737279) B3737279
theorem B6644051 : Blo 1967435 6644051 := bstep (se 1 (by rfl) ⟨4983038, by rfl⟩ : syracuseStep 6644051 = 9966077) B9966077
theorem B4429367 : Blo 1967435 4429367 := bstep (se 1 (by rfl) ⟨3322025, by rfl⟩ : syracuseStep 4429367 = 6644051) B6644051
theorem B2952911 : Blo 1967435 2952911 := bstep (se 1 (by rfl) ⟨2214683, by rfl⟩ : syracuseStep 2952911 = 4429367) B4429367
theorem B1968607 : Blo 1967435 1968607 := bstep (se 1 (by rfl) ⟨1476455, by rfl⟩ : syracuseStep 1968607 = 2952911) B2952911
theorem B2952917 : Blo 1967435 2952917 := bbase (se 7 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 2952917 = 69209) (by norm_num)
theorem B1968611 : Blo 1967435 1968611 := bstep (se 1 (by rfl) ⟨1476458, by rfl⟩ : syracuseStep 1968611 = 2952917) B2952917
theorem B68189141 : Blo 1967435 68189141 := bbase (se 7 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 68189141 = 1598183) (by norm_num)
theorem B45459427 : Blo 1967435 45459427 := bstep (se 1 (by rfl) ⟨34094570, by rfl⟩ : syracuseStep 45459427 = 68189141) B68189141
theorem B60612569 : Blo 1967435 60612569 := bstep (se 2 (by rfl) ⟨22729713, by rfl⟩ : syracuseStep 60612569 = 45459427) B45459427
theorem B40408379 : Blo 1967435 40408379 := bstep (se 1 (by rfl) ⟨30306284, by rfl⟩ : syracuseStep 40408379 = 60612569) B60612569
theorem B26938919 : Blo 1967435 26938919 := bstep (se 1 (by rfl) ⟨20204189, by rfl⟩ : syracuseStep 26938919 = 40408379) B40408379
theorem B17959279 : Blo 1967435 17959279 := bstep (se 1 (by rfl) ⟨13469459, by rfl⟩ : syracuseStep 17959279 = 26938919) B26938919
theorem B23945705 : Blo 1967435 23945705 := bstep (se 2 (by rfl) ⟨8979639, by rfl⟩ : syracuseStep 23945705 = 17959279) B17959279
theorem B15963803 : Blo 1967435 15963803 := bstep (se 1 (by rfl) ⟨11972852, by rfl⟩ : syracuseStep 15963803 = 23945705) B23945705
theorem B10642535 : Blo 1967435 10642535 := bstep (se 1 (by rfl) ⟨7981901, by rfl⟩ : syracuseStep 10642535 = 15963803) B15963803
theorem B7095023 : Blo 1967435 7095023 := bstep (se 1 (by rfl) ⟨5321267, by rfl⟩ : syracuseStep 7095023 = 10642535) B10642535
theorem B4730015 : Blo 1967435 4730015 := bstep (se 1 (by rfl) ⟨3547511, by rfl⟩ : syracuseStep 4730015 = 7095023) B7095023
theorem B3153343 : Blo 1967435 3153343 := bstep (se 1 (by rfl) ⟨2365007, by rfl⟩ : syracuseStep 3153343 = 4730015) B4730015
theorem B4204457 : Blo 1967435 4204457 := bstep (se 2 (by rfl) ⟨1576671, by rfl⟩ : syracuseStep 4204457 = 3153343) B3153343
theorem B2802971 : Blo 1967435 2802971 := bstep (se 1 (by rfl) ⟨2102228, by rfl⟩ : syracuseStep 2802971 = 4204457) B4204457
theorem B7474589 : Blo 1967435 7474589 := bstep (se 3 (by rfl) ⟨1401485, by rfl⟩ : syracuseStep 7474589 = 2802971) B2802971
theorem B4983059 : Blo 1967435 4983059 := bstep (se 1 (by rfl) ⟨3737294, by rfl⟩ : syracuseStep 4983059 = 7474589) B7474589
theorem B3322039 : Blo 1967435 3322039 := bstep (se 1 (by rfl) ⟨2491529, by rfl⟩ : syracuseStep 3322039 = 4983059) B4983059
theorem B4429385 : Blo 1967435 4429385 := bstep (se 2 (by rfl) ⟨1661019, by rfl⟩ : syracuseStep 4429385 = 3322039) B3322039
theorem B2952923 : Blo 1967435 2952923 := bstep (se 1 (by rfl) ⟨2214692, by rfl⟩ : syracuseStep 2952923 = 4429385) B4429385
theorem B1968615 : Blo 1967435 1968615 := bstep (se 1 (by rfl) ⟨1476461, by rfl⟩ : syracuseStep 1968615 = 2952923) B2952923
theorem B2214697 : Blo 1967435 2214697 := bbase (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) (by norm_num)
theorem B2952929 : Blo 1967435 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B1968619 : Blo 1967435 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B3547525 : Blo 1967435 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B4730033 : Blo 1967435 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B12613421 : Blo 1967435 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B8408947 : Blo 1967435 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B11211929 : Blo 1967435 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B7474619 : Blo 1967435 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B4983079 : Blo 1967435 4983079 := bstep (se 1 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 4983079 = 7474619) B7474619
theorem B6644105 : Blo 1967435 6644105 := bstep (se 2 (by rfl) ⟨2491539, by rfl⟩ : syracuseStep 6644105 = 4983079) B4983079
theorem B4429403 : Blo 1967435 4429403 := bstep (se 1 (by rfl) ⟨3322052, by rfl⟩ : syracuseStep 4429403 = 6644105) B6644105
theorem B2952935 : Blo 1967435 2952935 := bstep (se 1 (by rfl) ⟨2214701, by rfl⟩ : syracuseStep 2952935 = 4429403) B4429403
theorem B1968623 : Blo 1967435 1968623 := bstep (se 1 (by rfl) ⟨1476467, by rfl⟩ : syracuseStep 1968623 = 2952935) B2952935
theorem B2952941 : Blo 1967435 2952941 := bbase (se 3 (by rfl) ⟨553676, by rfl⟩ : syracuseStep 2952941 = 1107353) (by norm_num)
theorem B1968627 : Blo 1967435 1968627 := bstep (se 1 (by rfl) ⟨1476470, by rfl⟩ : syracuseStep 1968627 = 2952941) B2952941
theorem B4429421 : Blo 1967435 4429421 := bbase (se 3 (by rfl) ⟨830516, by rfl⟩ : syracuseStep 4429421 = 1661033) (by norm_num)
theorem B2952947 : Blo 1967435 2952947 := bstep (se 1 (by rfl) ⟨2214710, by rfl⟩ : syracuseStep 2952947 = 4429421) B4429421
theorem B1968631 : Blo 1967435 1968631 := bstep (se 1 (by rfl) ⟨1476473, by rfl⟩ : syracuseStep 1968631 = 2952947) B2952947
theorem B3737333 : Blo 1967435 3737333 := bbase (se 5 (by rfl) ⟨175187, by rfl⟩ : syracuseStep 3737333 = 350375) (by norm_num)
theorem B2491555 : Blo 1967435 2491555 := bstep (se 1 (by rfl) ⟨1868666, by rfl⟩ : syracuseStep 2491555 = 3737333) B3737333
theorem B3322073 : Blo 1967435 3322073 := bstep (se 2 (by rfl) ⟨1245777, by rfl⟩ : syracuseStep 3322073 = 2491555) B2491555
theorem B2214715 : Blo 1967435 2214715 := bstep (se 1 (by rfl) ⟨1661036, by rfl⟩ : syracuseStep 2214715 = 3322073) B3322073
theorem B2952953 : Blo 1967435 2952953 := bstep (se 2 (by rfl) ⟨1107357, by rfl⟩ : syracuseStep 2952953 = 2214715) B2214715
theorem B1968635 : Blo 1967435 1968635 := bstep (se 1 (by rfl) ⟨1476476, by rfl⟩ : syracuseStep 1968635 = 2952953) B2952953
theorem B5120021 : Blo 1967435 5120021 := bbase (se 6 (by rfl) ⟨120000, by rfl⟩ : syracuseStep 5120021 = 240001) (by norm_num)
theorem B3413347 : Blo 1967435 3413347 := bstep (se 1 (by rfl) ⟨2560010, by rfl⟩ : syracuseStep 3413347 = 5120021) B5120021
theorem B18204517 : Blo 1967435 18204517 := bstep (se 4 (by rfl) ⟨1706673, by rfl⟩ : syracuseStep 18204517 = 3413347) B3413347
theorem B97090757 : Blo 1967435 97090757 := bstep (se 4 (by rfl) ⟨9102258, by rfl⟩ : syracuseStep 97090757 = 18204517) B18204517
theorem B64727171 : Blo 1967435 64727171 := bstep (se 1 (by rfl) ⟨48545378, by rfl⟩ : syracuseStep 64727171 = 97090757) B97090757
theorem B43151447 : Blo 1967435 43151447 := bstep (se 1 (by rfl) ⟨32363585, by rfl⟩ : syracuseStep 43151447 = 64727171) B64727171
theorem B28767631 : Blo 1967435 28767631 := bstep (se 1 (by rfl) ⟨21575723, by rfl⟩ : syracuseStep 28767631 = 43151447) B43151447
theorem B38356841 : Blo 1967435 38356841 := bstep (se 2 (by rfl) ⟨14383815, by rfl⟩ : syracuseStep 38356841 = 28767631) B28767631
theorem B25571227 : Blo 1967435 25571227 := bstep (se 1 (by rfl) ⟨19178420, by rfl⟩ : syracuseStep 25571227 = 38356841) B38356841
theorem B34094969 : Blo 1967435 34094969 := bstep (se 2 (by rfl) ⟨12785613, by rfl⟩ : syracuseStep 34094969 = 25571227) B25571227
theorem B22729979 : Blo 1967435 22729979 := bstep (se 1 (by rfl) ⟨17047484, by rfl⟩ : syracuseStep 22729979 = 34094969) B34094969
theorem B15153319 : Blo 1967435 15153319 := bstep (se 1 (by rfl) ⟨11364989, by rfl⟩ : syracuseStep 15153319 = 22729979) B22729979
theorem B20204425 : Blo 1967435 20204425 := bstep (se 2 (by rfl) ⟨7576659, by rfl⟩ : syracuseStep 20204425 = 15153319) B15153319
theorem B26939233 : Blo 1967435 26939233 := bstep (se 2 (by rfl) ⟨10102212, by rfl⟩ : syracuseStep 26939233 = 20204425) B20204425
theorem B35918977 : Blo 1967435 35918977 := bstep (se 2 (by rfl) ⟨13469616, by rfl⟩ : syracuseStep 35918977 = 26939233) B26939233
theorem B47891969 : Blo 1967435 47891969 := bstep (se 2 (by rfl) ⟨17959488, by rfl⟩ : syracuseStep 47891969 = 35918977) B35918977
theorem B31927979 : Blo 1967435 31927979 := bstep (se 1 (by rfl) ⟨23945984, by rfl⟩ : syracuseStep 31927979 = 47891969) B47891969
theorem B85141277 : Blo 1967435 85141277 := bstep (se 3 (by rfl) ⟨15963989, by rfl⟩ : syracuseStep 85141277 = 31927979) B31927979
theorem B56760851 : Blo 1967435 56760851 := bstep (se 1 (by rfl) ⟨42570638, by rfl⟩ : syracuseStep 56760851 = 85141277) B85141277
theorem B37840567 : Blo 1967435 37840567 := bstep (se 1 (by rfl) ⟨28380425, by rfl⟩ : syracuseStep 37840567 = 56760851) B56760851
theorem B50454089 : Blo 1967435 50454089 := bstep (se 2 (by rfl) ⟨18920283, by rfl⟩ : syracuseStep 50454089 = 37840567) B37840567
theorem B33636059 : Blo 1967435 33636059 := bstep (se 1 (by rfl) ⟨25227044, by rfl⟩ : syracuseStep 33636059 = 50454089) B50454089
theorem B22424039 : Blo 1967435 22424039 := bstep (se 1 (by rfl) ⟨16818029, by rfl⟩ : syracuseStep 22424039 = 33636059) B33636059
theorem B14949359 : Blo 1967435 14949359 := bstep (se 1 (by rfl) ⟨11212019, by rfl⟩ : syracuseStep 14949359 = 22424039) B22424039
theorem B9966239 : Blo 1967435 9966239 := bstep (se 1 (by rfl) ⟨7474679, by rfl⟩ : syracuseStep 9966239 = 14949359) B14949359
theorem B6644159 : Blo 1967435 6644159 := bstep (se 1 (by rfl) ⟨4983119, by rfl⟩ : syracuseStep 6644159 = 9966239) B9966239
theorem B4429439 : Blo 1967435 4429439 := bstep (se 1 (by rfl) ⟨3322079, by rfl⟩ : syracuseStep 4429439 = 6644159) B6644159
theorem B2952959 : Blo 1967435 2952959 := bstep (se 1 (by rfl) ⟨2214719, by rfl⟩ : syracuseStep 2952959 = 4429439) B4429439
theorem B1968639 : Blo 1967435 1968639 := bstep (se 1 (by rfl) ⟨1476479, by rfl⟩ : syracuseStep 1968639 = 2952959) B2952959
theorem B2952965 : Blo 1967435 2952965 := bbase (se 4 (by rfl) ⟨276840, by rfl⟩ : syracuseStep 2952965 = 553681) (by norm_num)
theorem B1968643 : Blo 1967435 1968643 := bstep (se 1 (by rfl) ⟨1476482, by rfl⟩ : syracuseStep 1968643 = 2952965) B2952965
theorem B3322093 : Blo 1967435 3322093 := bbase (se 3 (by rfl) ⟨622892, by rfl⟩ : syracuseStep 3322093 = 1245785) (by norm_num)
theorem B4429457 : Blo 1967435 4429457 := bstep (se 2 (by rfl) ⟨1661046, by rfl⟩ : syracuseStep 4429457 = 3322093) B3322093
theorem B2952971 : Blo 1967435 2952971 := bstep (se 1 (by rfl) ⟨2214728, by rfl⟩ : syracuseStep 2952971 = 4429457) B4429457
theorem B1968647 : Blo 1967435 1968647 := bstep (se 1 (by rfl) ⟨1476485, by rfl⟩ : syracuseStep 1968647 = 2952971) B2952971
theorem B2214733 : Blo 1967435 2214733 := bbase (se 3 (by rfl) ⟨415262, by rfl⟩ : syracuseStep 2214733 = 830525) (by norm_num)
theorem B2952977 : Blo 1967435 2952977 := bstep (se 2 (by rfl) ⟨1107366, by rfl⟩ : syracuseStep 2952977 = 2214733) B2214733
theorem B1968651 : Blo 1967435 1968651 := bstep (se 1 (by rfl) ⟨1476488, by rfl⟩ : syracuseStep 1968651 = 2952977) B2952977
theorem B6644213 : Blo 1967435 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B4429475 : Blo 1967435 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B2952983 : Blo 1967435 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B1968655 : Blo 1967435 1968655 := bstep (se 1 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 1968655 = 2952983) B2952983
theorem B2952989 : Blo 1967435 2952989 := bbase (se 3 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 2952989 = 1107371) (by norm_num)
theorem B1968659 : Blo 1967435 1968659 := bstep (se 1 (by rfl) ⟨1476494, by rfl⟩ : syracuseStep 1968659 = 2952989) B2952989
theorem B4429493 : Blo 1967435 4429493 := bbase (se 5 (by rfl) ⟨207632, by rfl⟩ : syracuseStep 4429493 = 415265) (by norm_num)
theorem B2952995 : Blo 1967435 2952995 := bstep (se 1 (by rfl) ⟨2214746, by rfl⟩ : syracuseStep 2952995 = 4429493) B4429493
theorem B1968663 : Blo 1967435 1968663 := bstep (se 1 (by rfl) ⟨1476497, by rfl⟩ : syracuseStep 1968663 = 2952995) B2952995
theorem B11212181 : Blo 1967435 11212181 := bbase (se 6 (by rfl) ⟨262785, by rfl⟩ : syracuseStep 11212181 = 525571) (by norm_num)
theorem B7474787 : Blo 1967435 7474787 := bstep (se 1 (by rfl) ⟨5606090, by rfl⟩ : syracuseStep 7474787 = 11212181) B11212181
theorem B4983191 : Blo 1967435 4983191 := bstep (se 1 (by rfl) ⟨3737393, by rfl⟩ : syracuseStep 4983191 = 7474787) B7474787
theorem B3322127 : Blo 1967435 3322127 := bstep (se 1 (by rfl) ⟨2491595, by rfl⟩ : syracuseStep 3322127 = 4983191) B4983191
theorem B2214751 : Blo 1967435 2214751 := bstep (se 1 (by rfl) ⟨1661063, by rfl⟩ : syracuseStep 2214751 = 3322127) B3322127
theorem B2953001 : Blo 1967435 2953001 := bstep (se 2 (by rfl) ⟨1107375, by rfl⟩ : syracuseStep 2953001 = 2214751) B2214751
theorem B1968667 : Blo 1967435 1968667 := bstep (se 1 (by rfl) ⟨1476500, by rfl⟩ : syracuseStep 1968667 = 2953001) B2953001
theorem B5606101 : Blo 1967435 5606101 := bbase (se 7 (by rfl) ⟨65696, by rfl⟩ : syracuseStep 5606101 = 131393) (by norm_num)
theorem B7474801 : Blo 1967435 7474801 := bstep (se 2 (by rfl) ⟨2803050, by rfl⟩ : syracuseStep 7474801 = 5606101) B5606101
theorem B9966401 : Blo 1967435 9966401 := bstep (se 2 (by rfl) ⟨3737400, by rfl⟩ : syracuseStep 9966401 = 7474801) B7474801
theorem B6644267 : Blo 1967435 6644267 := bstep (se 1 (by rfl) ⟨4983200, by rfl⟩ : syracuseStep 6644267 = 9966401) B9966401
theorem B4429511 : Blo 1967435 4429511 := bstep (se 1 (by rfl) ⟨3322133, by rfl⟩ : syracuseStep 4429511 = 6644267) B6644267
theorem B2953007 : Blo 1967435 2953007 := bstep (se 1 (by rfl) ⟨2214755, by rfl⟩ : syracuseStep 2953007 = 4429511) B4429511
theorem B1968671 : Blo 1967435 1968671 := bstep (se 1 (by rfl) ⟨1476503, by rfl⟩ : syracuseStep 1968671 = 2953007) B2953007
theorem B2953013 : Blo 1967435 2953013 := bbase (se 5 (by rfl) ⟨138422, by rfl⟩ : syracuseStep 2953013 = 276845) (by norm_num)
theorem B1968675 : Blo 1967435 1968675 := bstep (se 1 (by rfl) ⟨1476506, by rfl⟩ : syracuseStep 1968675 = 2953013) B2953013
theorem B4983221 : Blo 1967435 4983221 := bbase (se 5 (by rfl) ⟨233588, by rfl⟩ : syracuseStep 4983221 = 467177) (by norm_num)
theorem B3322147 : Blo 1967435 3322147 := bstep (se 1 (by rfl) ⟨2491610, by rfl⟩ : syracuseStep 3322147 = 4983221) B4983221
theorem B4429529 : Blo 1967435 4429529 := bstep (se 2 (by rfl) ⟨1661073, by rfl⟩ : syracuseStep 4429529 = 3322147) B3322147
theorem B2953019 : Blo 1967435 2953019 := bstep (se 1 (by rfl) ⟨2214764, by rfl⟩ : syracuseStep 2953019 = 4429529) B4429529
theorem B1968679 : Blo 1967435 1968679 := bstep (se 1 (by rfl) ⟨1476509, by rfl⟩ : syracuseStep 1968679 = 2953019) B2953019
theorem B2214769 : Blo 1967435 2214769 := bbase (se 2 (by rfl) ⟨830538, by rfl⟩ : syracuseStep 2214769 = 1661077) (by norm_num)
theorem B2953025 : Blo 1967435 2953025 := bstep (se 2 (by rfl) ⟨1107384, by rfl⟩ : syracuseStep 2953025 = 2214769) B2214769
theorem B1968683 : Blo 1967435 1968683 := bstep (se 1 (by rfl) ⟨1476512, by rfl⟩ : syracuseStep 1968683 = 2953025) B2953025
theorem B8409221 : Blo 1967435 8409221 := bbase (se 4 (by rfl) ⟨788364, by rfl⟩ : syracuseStep 8409221 = 1576729) (by norm_num)
theorem B5606147 : Blo 1967435 5606147 := bstep (se 1 (by rfl) ⟨4204610, by rfl⟩ : syracuseStep 5606147 = 8409221) B8409221
theorem B3737431 : Blo 1967435 3737431 := bstep (se 1 (by rfl) ⟨2803073, by rfl⟩ : syracuseStep 3737431 = 5606147) B5606147
theorem B4983241 : Blo 1967435 4983241 := bstep (se 2 (by rfl) ⟨1868715, by rfl⟩ : syracuseStep 4983241 = 3737431) B3737431
theorem B6644321 : Blo 1967435 6644321 := bstep (se 2 (by rfl) ⟨2491620, by rfl⟩ : syracuseStep 6644321 = 4983241) B4983241
theorem B4429547 : Blo 1967435 4429547 := bstep (se 1 (by rfl) ⟨3322160, by rfl⟩ : syracuseStep 4429547 = 6644321) B6644321
theorem B2953031 : Blo 1967435 2953031 := bstep (se 1 (by rfl) ⟨2214773, by rfl⟩ : syracuseStep 2953031 = 4429547) B4429547
theorem B1968687 : Blo 1967435 1968687 := bstep (se 1 (by rfl) ⟨1476515, by rfl⟩ : syracuseStep 1968687 = 2953031) B2953031
theorem B2953037 : Blo 1967435 2953037 := bbase (se 3 (by rfl) ⟨553694, by rfl⟩ : syracuseStep 2953037 = 1107389) (by norm_num)
theorem B1968691 : Blo 1967435 1968691 := bstep (se 1 (by rfl) ⟨1476518, by rfl⟩ : syracuseStep 1968691 = 2953037) B2953037
theorem B4429565 : Blo 1967435 4429565 := bbase (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) (by norm_num)
theorem B2953043 : Blo 1967435 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B1968695 : Blo 1967435 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B3322181 : Blo 1967435 3322181 := bbase (se 4 (by rfl) ⟨311454, by rfl⟩ : syracuseStep 3322181 = 622909) (by norm_num)
theorem B2214787 : Blo 1967435 2214787 := bstep (se 1 (by rfl) ⟨1661090, by rfl⟩ : syracuseStep 2214787 = 3322181) B3322181
theorem B2953049 : Blo 1967435 2953049 := bstep (se 2 (by rfl) ⟨1107393, by rfl⟩ : syracuseStep 2953049 = 2214787) B2214787
theorem B1968699 : Blo 1967435 1968699 := bstep (se 1 (by rfl) ⟨1476524, by rfl⟩ : syracuseStep 1968699 = 2953049) B2953049
theorem B14949845 : Blo 1967435 14949845 := bbase (se 7 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 14949845 = 350387) (by norm_num)
theorem B9966563 : Blo 1967435 9966563 := bstep (se 1 (by rfl) ⟨7474922, by rfl⟩ : syracuseStep 9966563 = 14949845) B14949845
theorem B6644375 : Blo 1967435 6644375 := bstep (se 1 (by rfl) ⟨4983281, by rfl⟩ : syracuseStep 6644375 = 9966563) B9966563
theorem B4429583 : Blo 1967435 4429583 := bstep (se 1 (by rfl) ⟨3322187, by rfl⟩ : syracuseStep 4429583 = 6644375) B6644375
theorem B2953055 : Blo 1967435 2953055 := bstep (se 1 (by rfl) ⟨2214791, by rfl⟩ : syracuseStep 2953055 = 4429583) B4429583
theorem B1968703 : Blo 1967435 1968703 := bstep (se 1 (by rfl) ⟨1476527, by rfl⟩ : syracuseStep 1968703 = 2953055) B2953055
theorem B2953061 : Blo 1967435 2953061 := bbase (se 4 (by rfl) ⟨276849, by rfl⟩ : syracuseStep 2953061 = 553699) (by norm_num)
theorem B1968707 : Blo 1967435 1968707 := bstep (se 1 (by rfl) ⟨1476530, by rfl⟩ : syracuseStep 1968707 = 2953061) B2953061
theorem B3737477 : Blo 1967435 3737477 := bbase (se 4 (by rfl) ⟨350388, by rfl⟩ : syracuseStep 3737477 = 700777) (by norm_num)
theorem B2491651 : Blo 1967435 2491651 := bstep (se 1 (by rfl) ⟨1868738, by rfl⟩ : syracuseStep 2491651 = 3737477) B3737477
theorem B3322201 : Blo 1967435 3322201 := bstep (se 2 (by rfl) ⟨1245825, by rfl⟩ : syracuseStep 3322201 = 2491651) B2491651
theorem B4429601 : Blo 1967435 4429601 := bstep (se 2 (by rfl) ⟨1661100, by rfl⟩ : syracuseStep 4429601 = 3322201) B3322201
theorem B2953067 : Blo 1967435 2953067 := bstep (se 1 (by rfl) ⟨2214800, by rfl⟩ : syracuseStep 2953067 = 4429601) B4429601
theorem B1968711 : Blo 1967435 1968711 := bstep (se 1 (by rfl) ⟨1476533, by rfl⟩ : syracuseStep 1968711 = 2953067) B2953067
theorem B2214805 : Blo 1967435 2214805 := bbase (se 6 (by rfl) ⟨51909, by rfl⟩ : syracuseStep 2214805 = 103819) (by norm_num)
theorem B2953073 : Blo 1967435 2953073 := bstep (se 2 (by rfl) ⟨1107402, by rfl⟩ : syracuseStep 2953073 = 2214805) B2214805
theorem B1968715 : Blo 1967435 1968715 := bstep (se 1 (by rfl) ⟨1476536, by rfl⟩ : syracuseStep 1968715 = 2953073) B2953073
theorem B2491661 : Blo 1967435 2491661 := bbase (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) (by norm_num)
theorem B6644429 : Blo 1967435 6644429 := bstep (se 3 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 6644429 = 2491661) B2491661
theorem B4429619 : Blo 1967435 4429619 := bstep (se 1 (by rfl) ⟨3322214, by rfl⟩ : syracuseStep 4429619 = 6644429) B6644429
theorem B2953079 : Blo 1967435 2953079 := bstep (se 1 (by rfl) ⟨2214809, by rfl⟩ : syracuseStep 2953079 = 4429619) B4429619
theorem B1968719 : Blo 1967435 1968719 := bstep (se 1 (by rfl) ⟨1476539, by rfl⟩ : syracuseStep 1968719 = 2953079) B2953079
theorem B2953085 : Blo 1967435 2953085 := bbase (se 3 (by rfl) ⟨553703, by rfl⟩ : syracuseStep 2953085 = 1107407) (by norm_num)
theorem B1968723 : Blo 1967435 1968723 := bstep (se 1 (by rfl) ⟨1476542, by rfl⟩ : syracuseStep 1968723 = 2953085) B2953085
theorem B4429637 : Blo 1967435 4429637 := bbase (se 4 (by rfl) ⟨415278, by rfl⟩ : syracuseStep 4429637 = 830557) (by norm_num)
theorem B2953091 : Blo 1967435 2953091 := bstep (se 1 (by rfl) ⟨2214818, by rfl⟩ : syracuseStep 2953091 = 4429637) B4429637
theorem B1968727 : Blo 1967435 1968727 := bstep (se 1 (by rfl) ⟨1476545, by rfl⟩ : syracuseStep 1968727 = 2953091) B2953091
theorem B3367565 : Blo 1967435 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B2245043 : Blo 1967435 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B5986781 : Blo 1967435 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B3991187 : Blo 1967435 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B2660791 : Blo 1967435 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B3547721 : Blo 1967435 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B2365147 : Blo 1967435 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B3153529 : Blo 1967435 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B4204705 : Blo 1967435 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B5606273 : Blo 1967435 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B3737515 : Blo 1967435 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B4983353 : Blo 1967435 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B3322235 : Blo 1967435 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B2214823 : Blo 1967435 2214823 := bstep (se 1 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 2214823 = 3322235) B3322235
theorem B2953097 : Blo 1967435 2953097 := bstep (se 2 (by rfl) ⟨1107411, by rfl⟩ : syracuseStep 2953097 = 2214823) B2214823
theorem B1968731 : Blo 1967435 1968731 := bstep (se 1 (by rfl) ⟨1476548, by rfl⟩ : syracuseStep 1968731 = 2953097) B2953097
theorem B9966725 : Blo 1967435 9966725 := bbase (se 4 (by rfl) ⟨934380, by rfl⟩ : syracuseStep 9966725 = 1868761) (by norm_num)
theorem B6644483 : Blo 1967435 6644483 := bstep (se 1 (by rfl) ⟨4983362, by rfl⟩ : syracuseStep 6644483 = 9966725) B9966725
theorem B4429655 : Blo 1967435 4429655 := bstep (se 1 (by rfl) ⟨3322241, by rfl⟩ : syracuseStep 4429655 = 6644483) B6644483
theorem B2953103 : Blo 1967435 2953103 := bstep (se 1 (by rfl) ⟨2214827, by rfl⟩ : syracuseStep 2953103 = 4429655) B4429655
theorem B1968735 : Blo 1967435 1968735 := bstep (se 1 (by rfl) ⟨1476551, by rfl⟩ : syracuseStep 1968735 = 2953103) B2953103
theorem B2953109 : Blo 1967435 2953109 := bbase (se 6 (by rfl) ⟨69213, by rfl⟩ : syracuseStep 2953109 = 138427) (by norm_num)
theorem B1968739 : Blo 1967435 1968739 := bstep (se 1 (by rfl) ⟨1476554, by rfl⟩ : syracuseStep 1968739 = 2953109) B2953109
theorem B2102365 : Blo 1967435 2102365 := bbase (se 3 (by rfl) ⟨394193, by rfl⟩ : syracuseStep 2102365 = 788387) (by norm_num)
theorem B11212613 : Blo 1967435 11212613 := bstep (se 4 (by rfl) ⟨1051182, by rfl⟩ : syracuseStep 11212613 = 2102365) B2102365
theorem B7475075 : Blo 1967435 7475075 := bstep (se 1 (by rfl) ⟨5606306, by rfl⟩ : syracuseStep 7475075 = 11212613) B11212613
theorem B4983383 : Blo 1967435 4983383 := bstep (se 1 (by rfl) ⟨3737537, by rfl⟩ : syracuseStep 4983383 = 7475075) B7475075
theorem B3322255 : Blo 1967435 3322255 := bstep (se 1 (by rfl) ⟨2491691, by rfl⟩ : syracuseStep 3322255 = 4983383) B4983383
theorem B4429673 : Blo 1967435 4429673 := bstep (se 2 (by rfl) ⟨1661127, by rfl⟩ : syracuseStep 4429673 = 3322255) B3322255
theorem B2953115 : Blo 1967435 2953115 := bstep (se 1 (by rfl) ⟨2214836, by rfl⟩ : syracuseStep 2953115 = 4429673) B4429673
theorem B1968743 : Blo 1967435 1968743 := bstep (se 1 (by rfl) ⟨1476557, by rfl⟩ : syracuseStep 1968743 = 2953115) B2953115
theorem B2214841 : Blo 1967435 2214841 := bbase (se 2 (by rfl) ⟨830565, by rfl⟩ : syracuseStep 2214841 = 1661131) (by norm_num)
theorem B2953121 : Blo 1967435 2953121 := bstep (se 2 (by rfl) ⟨1107420, by rfl⟩ : syracuseStep 2953121 = 2214841) B2214841
theorem B1968747 : Blo 1967435 1968747 := bstep (se 1 (by rfl) ⟨1476560, by rfl⟩ : syracuseStep 1968747 = 2953121) B2953121
theorem B4730341 : Blo 1967435 4730341 := bbase (se 4 (by rfl) ⟨443469, by rfl⟩ : syracuseStep 4730341 = 886939) (by norm_num)
theorem B6307121 : Blo 1967435 6307121 := bstep (se 2 (by rfl) ⟨2365170, by rfl⟩ : syracuseStep 6307121 = 4730341) B4730341
theorem B4204747 : Blo 1967435 4204747 := bstep (se 1 (by rfl) ⟨3153560, by rfl⟩ : syracuseStep 4204747 = 6307121) B6307121
theorem B5606329 : Blo 1967435 5606329 := bstep (se 2 (by rfl) ⟨2102373, by rfl⟩ : syracuseStep 5606329 = 4204747) B4204747
theorem B7475105 : Blo 1967435 7475105 := bstep (se 2 (by rfl) ⟨2803164, by rfl⟩ : syracuseStep 7475105 = 5606329) B5606329
theorem B4983403 : Blo 1967435 4983403 := bstep (se 1 (by rfl) ⟨3737552, by rfl⟩ : syracuseStep 4983403 = 7475105) B7475105
theorem B6644537 : Blo 1967435 6644537 := bstep (se 2 (by rfl) ⟨2491701, by rfl⟩ : syracuseStep 6644537 = 4983403) B4983403
theorem B4429691 : Blo 1967435 4429691 := bstep (se 1 (by rfl) ⟨3322268, by rfl⟩ : syracuseStep 4429691 = 6644537) B6644537
theorem B2953127 : Blo 1967435 2953127 := bstep (se 1 (by rfl) ⟨2214845, by rfl⟩ : syracuseStep 2953127 = 4429691) B4429691
theorem B1968751 : Blo 1967435 1968751 := bstep (se 1 (by rfl) ⟨1476563, by rfl⟩ : syracuseStep 1968751 = 2953127) B2953127
theorem B2953133 : Blo 1967435 2953133 := bbase (se 3 (by rfl) ⟨553712, by rfl⟩ : syracuseStep 2953133 = 1107425) (by norm_num)
theorem B1968755 : Blo 1967435 1968755 := bstep (se 1 (by rfl) ⟨1476566, by rfl⟩ : syracuseStep 1968755 = 2953133) B2953133
theorem B4429709 : Blo 1967435 4429709 := bbase (se 3 (by rfl) ⟨830570, by rfl⟩ : syracuseStep 4429709 = 1661141) (by norm_num)
theorem B2953139 : Blo 1967435 2953139 := bstep (se 1 (by rfl) ⟨2214854, by rfl⟩ : syracuseStep 2953139 = 4429709) B4429709
theorem B1968759 : Blo 1967435 1968759 := bstep (se 1 (by rfl) ⟨1476569, by rfl⟩ : syracuseStep 1968759 = 2953139) B2953139
theorem B2491717 : Blo 1967435 2491717 := bbase (se 4 (by rfl) ⟨233598, by rfl⟩ : syracuseStep 2491717 = 467197) (by norm_num)
theorem B3322289 : Blo 1967435 3322289 := bstep (se 2 (by rfl) ⟨1245858, by rfl⟩ : syracuseStep 3322289 = 2491717) B2491717
theorem B2214859 : Blo 1967435 2214859 := bstep (se 1 (by rfl) ⟨1661144, by rfl⟩ : syracuseStep 2214859 = 3322289) B3322289
theorem B2953145 : Blo 1967435 2953145 := bstep (se 2 (by rfl) ⟨1107429, by rfl⟩ : syracuseStep 2953145 = 2214859) B2214859
theorem B1968763 : Blo 1967435 1968763 := bstep (se 1 (by rfl) ⟨1476572, by rfl⟩ : syracuseStep 1968763 = 2953145) B2953145
theorem B9460757 : Blo 1967435 9460757 := bbase (se 6 (by rfl) ⟨221736, by rfl⟩ : syracuseStep 9460757 = 443473) (by norm_num)
theorem B25228685 : Blo 1967435 25228685 := bstep (se 3 (by rfl) ⟨4730378, by rfl⟩ : syracuseStep 25228685 = 9460757) B9460757
theorem B16819123 : Blo 1967435 16819123 := bstep (se 1 (by rfl) ⟨12614342, by rfl⟩ : syracuseStep 16819123 = 25228685) B25228685
theorem B22425497 : Blo 1967435 22425497 := bstep (se 2 (by rfl) ⟨8409561, by rfl⟩ : syracuseStep 22425497 = 16819123) B16819123
theorem B14950331 : Blo 1967435 14950331 := bstep (se 1 (by rfl) ⟨11212748, by rfl⟩ : syracuseStep 14950331 = 22425497) B22425497
theorem B9966887 : Blo 1967435 9966887 := bstep (se 1 (by rfl) ⟨7475165, by rfl⟩ : syracuseStep 9966887 = 14950331) B14950331
theorem B6644591 : Blo 1967435 6644591 := bstep (se 1 (by rfl) ⟨4983443, by rfl⟩ : syracuseStep 6644591 = 9966887) B9966887
theorem B4429727 : Blo 1967435 4429727 := bstep (se 1 (by rfl) ⟨3322295, by rfl⟩ : syracuseStep 4429727 = 6644591) B6644591
theorem B2953151 : Blo 1967435 2953151 := bstep (se 1 (by rfl) ⟨2214863, by rfl⟩ : syracuseStep 2953151 = 4429727) B4429727
theorem B1968767 : Blo 1967435 1968767 := bstep (se 1 (by rfl) ⟨1476575, by rfl⟩ : syracuseStep 1968767 = 2953151) B2953151
theorem B2953157 : Blo 1967435 2953157 := bbase (se 4 (by rfl) ⟨276858, by rfl⟩ : syracuseStep 2953157 = 553717) (by norm_num)
theorem B1968771 : Blo 1967435 1968771 := bstep (se 1 (by rfl) ⟨1476578, by rfl⟩ : syracuseStep 1968771 = 2953157) B2953157
theorem B3322309 : Blo 1967435 3322309 := bbase (se 4 (by rfl) ⟨311466, by rfl⟩ : syracuseStep 3322309 = 622933) (by norm_num)
theorem B4429745 : Blo 1967435 4429745 := bstep (se 2 (by rfl) ⟨1661154, by rfl⟩ : syracuseStep 4429745 = 3322309) B3322309
theorem B2953163 : Blo 1967435 2953163 := bstep (se 1 (by rfl) ⟨2214872, by rfl⟩ : syracuseStep 2953163 = 4429745) B4429745
theorem B1968775 : Blo 1967435 1968775 := bstep (se 1 (by rfl) ⟨1476581, by rfl⟩ : syracuseStep 1968775 = 2953163) B2953163
theorem B2214877 : Blo 1967435 2214877 := bbase (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) (by norm_num)
theorem B2953169 : Blo 1967435 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B1968779 : Blo 1967435 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B6644645 : Blo 1967435 6644645 := bbase (se 4 (by rfl) ⟨622935, by rfl⟩ : syracuseStep 6644645 = 1245871) (by norm_num)
theorem B4429763 : Blo 1967435 4429763 := bstep (se 1 (by rfl) ⟨3322322, by rfl⟩ : syracuseStep 4429763 = 6644645) B6644645
theorem B2953175 : Blo 1967435 2953175 := bstep (se 1 (by rfl) ⟨2214881, by rfl⟩ : syracuseStep 2953175 = 4429763) B4429763
theorem B1968783 : Blo 1967435 1968783 := bstep (se 1 (by rfl) ⟨1476587, by rfl⟩ : syracuseStep 1968783 = 2953175) B2953175
theorem B2953181 : Blo 1967435 2953181 := bbase (se 3 (by rfl) ⟨553721, by rfl⟩ : syracuseStep 2953181 = 1107443) (by norm_num)
theorem B1968787 : Blo 1967435 1968787 := bstep (se 1 (by rfl) ⟨1476590, by rfl⟩ : syracuseStep 1968787 = 2953181) B2953181
theorem B4429781 : Blo 1967435 4429781 := bbase (se 7 (by rfl) ⟨51911, by rfl⟩ : syracuseStep 4429781 = 103823) (by norm_num)
theorem B2953187 : Blo 1967435 2953187 := bstep (se 1 (by rfl) ⟨2214890, by rfl⟩ : syracuseStep 2953187 = 4429781) B4429781
theorem B1968791 : Blo 1967435 1968791 := bstep (se 1 (by rfl) ⟨1476593, by rfl⟩ : syracuseStep 1968791 = 2953187) B2953187
theorem B4262213 : Blo 1967435 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2841475 : Blo 1967435 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B3788633 : Blo 1967435 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B2525755 : Blo 1967435 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3367673 : Blo 1967435 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2245115 : Blo 1967435 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B5986973 : Blo 1967435 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B15965261 : Blo 1967435 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B10643507 : Blo 1967435 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B7095671 : Blo 1967435 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B4730447 : Blo 1967435 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B12614525 : Blo 1967435 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B8409683 : Blo 1967435 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B5606455 : Blo 1967435 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B7475273 : Blo 1967435 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B4983515 : Blo 1967435 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B3322343 : Blo 1967435 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B2214895 : Blo 1967435 2214895 := bstep (se 1 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 2214895 = 3322343) B3322343
theorem B2953193 : Blo 1967435 2953193 := bstep (se 2 (by rfl) ⟨1107447, by rfl⟩ : syracuseStep 2953193 = 2214895) B2214895
theorem B1968795 : Blo 1967435 1968795 := bstep (se 1 (by rfl) ⟨1476596, by rfl⟩ : syracuseStep 1968795 = 2953193) B2953193
theorem B3153637 : Blo 1967435 3153637 := bbase (se 4 (by rfl) ⟨295653, by rfl⟩ : syracuseStep 3153637 = 591307) (by norm_num)
theorem B16819397 : Blo 1967435 16819397 := bstep (se 4 (by rfl) ⟨1576818, by rfl⟩ : syracuseStep 16819397 = 3153637) B3153637
theorem B11212931 : Blo 1967435 11212931 := bstep (se 1 (by rfl) ⟨8409698, by rfl⟩ : syracuseStep 11212931 = 16819397) B16819397
theorem B7475287 : Blo 1967435 7475287 := bstep (se 1 (by rfl) ⟨5606465, by rfl⟩ : syracuseStep 7475287 = 11212931) B11212931
theorem B9967049 : Blo 1967435 9967049 := bstep (se 2 (by rfl) ⟨3737643, by rfl⟩ : syracuseStep 9967049 = 7475287) B7475287
theorem B6644699 : Blo 1967435 6644699 := bstep (se 1 (by rfl) ⟨4983524, by rfl⟩ : syracuseStep 6644699 = 9967049) B9967049
theorem B4429799 : Blo 1967435 4429799 := bstep (se 1 (by rfl) ⟨3322349, by rfl⟩ : syracuseStep 4429799 = 6644699) B6644699
theorem B2953199 : Blo 1967435 2953199 := bstep (se 1 (by rfl) ⟨2214899, by rfl⟩ : syracuseStep 2953199 = 4429799) B4429799
theorem B1968799 : Blo 1967435 1968799 := bstep (se 1 (by rfl) ⟨1476599, by rfl⟩ : syracuseStep 1968799 = 2953199) B2953199
theorem B2953205 : Blo 1967435 2953205 := bbase (se 5 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 2953205 = 276863) (by norm_num)
theorem B1968803 : Blo 1967435 1968803 := bstep (se 1 (by rfl) ⟨1476602, by rfl⟩ : syracuseStep 1968803 = 2953205) B2953205
theorem B6307301 : Blo 1967435 6307301 := bbase (se 4 (by rfl) ⟨591309, by rfl⟩ : syracuseStep 6307301 = 1182619) (by norm_num)
theorem B4204867 : Blo 1967435 4204867 := bstep (se 1 (by rfl) ⟨3153650, by rfl⟩ : syracuseStep 4204867 = 6307301) B6307301
theorem B5606489 : Blo 1967435 5606489 := bstep (se 2 (by rfl) ⟨2102433, by rfl⟩ : syracuseStep 5606489 = 4204867) B4204867
theorem B3737659 : Blo 1967435 3737659 := bstep (se 1 (by rfl) ⟨2803244, by rfl⟩ : syracuseStep 3737659 = 5606489) B5606489
theorem B4983545 : Blo 1967435 4983545 := bstep (se 2 (by rfl) ⟨1868829, by rfl⟩ : syracuseStep 4983545 = 3737659) B3737659
theorem B3322363 : Blo 1967435 3322363 := bstep (se 1 (by rfl) ⟨2491772, by rfl⟩ : syracuseStep 3322363 = 4983545) B4983545
theorem B4429817 : Blo 1967435 4429817 := bstep (se 2 (by rfl) ⟨1661181, by rfl⟩ : syracuseStep 4429817 = 3322363) B3322363
theorem B2953211 : Blo 1967435 2953211 := bstep (se 1 (by rfl) ⟨2214908, by rfl⟩ : syracuseStep 2953211 = 4429817) B4429817
theorem B1968807 : Blo 1967435 1968807 := bstep (se 1 (by rfl) ⟨1476605, by rfl⟩ : syracuseStep 1968807 = 2953211) B2953211
theorem B2214913 : Blo 1967435 2214913 := bbase (se 2 (by rfl) ⟨830592, by rfl⟩ : syracuseStep 2214913 = 1661185) (by norm_num)
theorem B2953217 : Blo 1967435 2953217 := bstep (se 2 (by rfl) ⟨1107456, by rfl⟩ : syracuseStep 2953217 = 2214913) B2214913
theorem B1968811 : Blo 1967435 1968811 := bstep (se 1 (by rfl) ⟨1476608, by rfl⟩ : syracuseStep 1968811 = 2953217) B2953217
theorem B4983565 : Blo 1967435 4983565 := bbase (se 3 (by rfl) ⟨934418, by rfl⟩ : syracuseStep 4983565 = 1868837) (by norm_num)
theorem B6644753 : Blo 1967435 6644753 := bstep (se 2 (by rfl) ⟨2491782, by rfl⟩ : syracuseStep 6644753 = 4983565) B4983565
theorem B4429835 : Blo 1967435 4429835 := bstep (se 1 (by rfl) ⟨3322376, by rfl⟩ : syracuseStep 4429835 = 6644753) B6644753
theorem B2953223 : Blo 1967435 2953223 := bstep (se 1 (by rfl) ⟨2214917, by rfl⟩ : syracuseStep 2953223 = 4429835) B4429835
theorem B1968815 : Blo 1967435 1968815 := bstep (se 1 (by rfl) ⟨1476611, by rfl⟩ : syracuseStep 1968815 = 2953223) B2953223
theorem B2953229 : Blo 1967435 2953229 := bbase (se 3 (by rfl) ⟨553730, by rfl⟩ : syracuseStep 2953229 = 1107461) (by norm_num)
theorem B1968819 : Blo 1967435 1968819 := bstep (se 1 (by rfl) ⟨1476614, by rfl⟩ : syracuseStep 1968819 = 2953229) B2953229
theorem B4429853 : Blo 1967435 4429853 := bbase (se 3 (by rfl) ⟨830597, by rfl⟩ : syracuseStep 4429853 = 1661195) (by norm_num)
theorem B2953235 : Blo 1967435 2953235 := bstep (se 1 (by rfl) ⟨2214926, by rfl⟩ : syracuseStep 2953235 = 4429853) B4429853
theorem B1968823 : Blo 1967435 1968823 := bstep (se 1 (by rfl) ⟨1476617, by rfl⟩ : syracuseStep 1968823 = 2953235) B2953235
theorem B3322397 : Blo 1967435 3322397 := bbase (se 3 (by rfl) ⟨622949, by rfl⟩ : syracuseStep 3322397 = 1245899) (by norm_num)
theorem B2214931 : Blo 1967435 2214931 := bstep (se 1 (by rfl) ⟨1661198, by rfl⟩ : syracuseStep 2214931 = 3322397) B3322397
theorem B2953241 : Blo 1967435 2953241 := bstep (se 2 (by rfl) ⟨1107465, by rfl⟩ : syracuseStep 2953241 = 2214931) B2214931
theorem B1968827 : Blo 1967435 1968827 := bstep (se 1 (by rfl) ⟨1476620, by rfl⟩ : syracuseStep 1968827 = 2953241) B2953241
theorem B7192613 : Blo 1967435 7192613 := bbase (se 4 (by rfl) ⟨674307, by rfl⟩ : syracuseStep 7192613 = 1348615) (by norm_num)
theorem B4795075 : Blo 1967435 4795075 := bstep (se 1 (by rfl) ⟨3596306, by rfl⟩ : syracuseStep 4795075 = 7192613) B7192613
theorem B6393433 : Blo 1967435 6393433 := bstep (se 2 (by rfl) ⟨2397537, by rfl⟩ : syracuseStep 6393433 = 4795075) B4795075
theorem B8524577 : Blo 1967435 8524577 := bstep (se 2 (by rfl) ⟨3196716, by rfl⟩ : syracuseStep 8524577 = 6393433) B6393433
theorem B5683051 : Blo 1967435 5683051 := bstep (se 1 (by rfl) ⟨4262288, by rfl⟩ : syracuseStep 5683051 = 8524577) B8524577
theorem B7577401 : Blo 1967435 7577401 := bstep (se 2 (by rfl) ⟨2841525, by rfl⟩ : syracuseStep 7577401 = 5683051) B5683051
theorem B10103201 : Blo 1967435 10103201 := bstep (se 2 (by rfl) ⟨3788700, by rfl⟩ : syracuseStep 10103201 = 7577401) B7577401
theorem B6735467 : Blo 1967435 6735467 := bstep (se 1 (by rfl) ⟨5051600, by rfl⟩ : syracuseStep 6735467 = 10103201) B10103201
theorem B4490311 : Blo 1967435 4490311 := bstep (se 1 (by rfl) ⟨3367733, by rfl⟩ : syracuseStep 4490311 = 6735467) B6735467
theorem B5987081 : Blo 1967435 5987081 := bstep (se 2 (by rfl) ⟨2245155, by rfl⟩ : syracuseStep 5987081 = 4490311) B4490311
theorem B15965549 : Blo 1967435 15965549 := bstep (se 3 (by rfl) ⟨2993540, by rfl⟩ : syracuseStep 15965549 = 5987081) B5987081
theorem B10643699 : Blo 1967435 10643699 := bstep (se 1 (by rfl) ⟨7982774, by rfl⟩ : syracuseStep 10643699 = 15965549) B15965549
theorem B7095799 : Blo 1967435 7095799 := bstep (se 1 (by rfl) ⟨5321849, by rfl⟩ : syracuseStep 7095799 = 10643699) B10643699
theorem B9461065 : Blo 1967435 9461065 := bstep (se 2 (by rfl) ⟨3547899, by rfl⟩ : syracuseStep 9461065 = 7095799) B7095799
theorem B12614753 : Blo 1967435 12614753 := bstep (se 2 (by rfl) ⟨4730532, by rfl⟩ : syracuseStep 12614753 = 9461065) B9461065
theorem B8409835 : Blo 1967435 8409835 := bstep (se 1 (by rfl) ⟨6307376, by rfl⟩ : syracuseStep 8409835 = 12614753) B12614753
theorem B11213113 : Blo 1967435 11213113 := bstep (se 2 (by rfl) ⟨4204917, by rfl⟩ : syracuseStep 11213113 = 8409835) B8409835
theorem B14950817 : Blo 1967435 14950817 := bstep (se 2 (by rfl) ⟨5606556, by rfl⟩ : syracuseStep 14950817 = 11213113) B11213113
theorem B9967211 : Blo 1967435 9967211 := bstep (se 1 (by rfl) ⟨7475408, by rfl⟩ : syracuseStep 9967211 = 14950817) B14950817
theorem B6644807 : Blo 1967435 6644807 := bstep (se 1 (by rfl) ⟨4983605, by rfl⟩ : syracuseStep 6644807 = 9967211) B9967211
theorem B4429871 : Blo 1967435 4429871 := bstep (se 1 (by rfl) ⟨3322403, by rfl⟩ : syracuseStep 4429871 = 6644807) B6644807
theorem B2953247 : Blo 1967435 2953247 := bstep (se 1 (by rfl) ⟨2214935, by rfl⟩ : syracuseStep 2953247 = 4429871) B4429871
theorem B1968831 : Blo 1967435 1968831 := bstep (se 1 (by rfl) ⟨1476623, by rfl⟩ : syracuseStep 1968831 = 2953247) B2953247
theorem B2953253 : Blo 1967435 2953253 := bbase (se 4 (by rfl) ⟨276867, by rfl⟩ : syracuseStep 2953253 = 553735) (by norm_num)
theorem B1968835 : Blo 1967435 1968835 := bstep (se 1 (by rfl) ⟨1476626, by rfl⟩ : syracuseStep 1968835 = 2953253) B2953253
theorem B2491813 : Blo 1967435 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B3322417 : Blo 1967435 3322417 := bstep (se 2 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 3322417 = 2491813) B2491813
theorem B4429889 : Blo 1967435 4429889 := bstep (se 2 (by rfl) ⟨1661208, by rfl⟩ : syracuseStep 4429889 = 3322417) B3322417
theorem B2953259 : Blo 1967435 2953259 := bstep (se 1 (by rfl) ⟨2214944, by rfl⟩ : syracuseStep 2953259 = 4429889) B4429889
theorem B1968839 : Blo 1967435 1968839 := bstep (se 1 (by rfl) ⟨1476629, by rfl⟩ : syracuseStep 1968839 = 2953259) B2953259
theorem B2214949 : Blo 1967435 2214949 := bbase (se 4 (by rfl) ⟨207651, by rfl⟩ : syracuseStep 2214949 = 415303) (by norm_num)
theorem B2953265 : Blo 1967435 2953265 := bstep (se 2 (by rfl) ⟨1107474, by rfl⟩ : syracuseStep 2953265 = 2214949) B2214949
theorem B1968843 : Blo 1967435 1968843 := bstep (se 1 (by rfl) ⟨1476632, by rfl⟩ : syracuseStep 1968843 = 2953265) B2953265
theorem B6307429 : Blo 1967435 6307429 := bbase (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) (by norm_num)
theorem B8409905 : Blo 1967435 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B5606603 : Blo 1967435 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B3737735 : Blo 1967435 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B2491823 : Blo 1967435 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B6644861 : Blo 1967435 6644861 := bstep (se 3 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 6644861 = 2491823) B2491823
theorem B4429907 : Blo 1967435 4429907 := bstep (se 1 (by rfl) ⟨3322430, by rfl⟩ : syracuseStep 4429907 = 6644861) B6644861
theorem B2953271 : Blo 1967435 2953271 := bstep (se 1 (by rfl) ⟨2214953, by rfl⟩ : syracuseStep 2953271 = 4429907) B4429907
theorem B1968847 : Blo 1967435 1968847 := bstep (se 1 (by rfl) ⟨1476635, by rfl⟩ : syracuseStep 1968847 = 2953271) B2953271
theorem B2953277 : Blo 1967435 2953277 := bbase (se 3 (by rfl) ⟨553739, by rfl⟩ : syracuseStep 2953277 = 1107479) (by norm_num)
theorem B1968851 : Blo 1967435 1968851 := bstep (se 1 (by rfl) ⟨1476638, by rfl⟩ : syracuseStep 1968851 = 2953277) B2953277
theorem B4429925 : Blo 1967435 4429925 := bbase (se 4 (by rfl) ⟨415305, by rfl⟩ : syracuseStep 4429925 = 830611) (by norm_num)
theorem B2953283 : Blo 1967435 2953283 := bstep (se 1 (by rfl) ⟨2214962, by rfl⟩ : syracuseStep 2953283 = 4429925) B4429925
theorem B1968855 : Blo 1967435 1968855 := bstep (se 1 (by rfl) ⟨1476641, by rfl⟩ : syracuseStep 1968855 = 2953283) B2953283
theorem B4983677 : Blo 1967435 4983677 := bbase (se 3 (by rfl) ⟨934439, by rfl⟩ : syracuseStep 4983677 = 1868879) (by norm_num)
theorem B3322451 : Blo 1967435 3322451 := bstep (se 1 (by rfl) ⟨2491838, by rfl⟩ : syracuseStep 3322451 = 4983677) B4983677
theorem B2214967 : Blo 1967435 2214967 := bstep (se 1 (by rfl) ⟨1661225, by rfl⟩ : syracuseStep 2214967 = 3322451) B3322451
theorem B2953289 : Blo 1967435 2953289 := bstep (se 2 (by rfl) ⟨1107483, by rfl⟩ : syracuseStep 2953289 = 2214967) B2214967
theorem B1968859 : Blo 1967435 1968859 := bstep (se 1 (by rfl) ⟨1476644, by rfl⟩ : syracuseStep 1968859 = 2953289) B2953289
theorem B3737765 : Blo 1967435 3737765 := bbase (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) (by norm_num)
theorem B9967373 : Blo 1967435 9967373 := bstep (se 3 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 9967373 = 3737765) B3737765
theorem B6644915 : Blo 1967435 6644915 := bstep (se 1 (by rfl) ⟨4983686, by rfl⟩ : syracuseStep 6644915 = 9967373) B9967373
theorem B4429943 : Blo 1967435 4429943 := bstep (se 1 (by rfl) ⟨3322457, by rfl⟩ : syracuseStep 4429943 = 6644915) B6644915
theorem B2953295 : Blo 1967435 2953295 := bstep (se 1 (by rfl) ⟨2214971, by rfl⟩ : syracuseStep 2953295 = 4429943) B4429943
theorem B1968863 : Blo 1967435 1968863 := bstep (se 1 (by rfl) ⟨1476647, by rfl⟩ : syracuseStep 1968863 = 2953295) B2953295
theorem B2953301 : Blo 1967435 2953301 := bbase (se 8 (by rfl) ⟨17304, by rfl⟩ : syracuseStep 2953301 = 34609) (by norm_num)
theorem B1968867 : Blo 1967435 1968867 := bstep (se 1 (by rfl) ⟨1476650, by rfl⟩ : syracuseStep 1968867 = 2953301) B2953301
theorem B18922517 : Blo 1967435 18922517 := bbase (se 6 (by rfl) ⟨443496, by rfl⟩ : syracuseStep 18922517 = 886993) (by norm_num)
theorem B12615011 : Blo 1967435 12615011 := bstep (se 1 (by rfl) ⟨9461258, by rfl⟩ : syracuseStep 12615011 = 18922517) B18922517
theorem B8410007 : Blo 1967435 8410007 := bstep (se 1 (by rfl) ⟨6307505, by rfl⟩ : syracuseStep 8410007 = 12615011) B12615011
theorem B5606671 : Blo 1967435 5606671 := bstep (se 1 (by rfl) ⟨4205003, by rfl⟩ : syracuseStep 5606671 = 8410007) B8410007
theorem B7475561 : Blo 1967435 7475561 := bstep (se 2 (by rfl) ⟨2803335, by rfl⟩ : syracuseStep 7475561 = 5606671) B5606671
theorem B4983707 : Blo 1967435 4983707 := bstep (se 1 (by rfl) ⟨3737780, by rfl⟩ : syracuseStep 4983707 = 7475561) B7475561
theorem B3322471 : Blo 1967435 3322471 := bstep (se 1 (by rfl) ⟨2491853, by rfl⟩ : syracuseStep 3322471 = 4983707) B4983707
theorem B4429961 : Blo 1967435 4429961 := bstep (se 2 (by rfl) ⟨1661235, by rfl⟩ : syracuseStep 4429961 = 3322471) B3322471
theorem B2953307 : Blo 1967435 2953307 := bstep (se 1 (by rfl) ⟨2214980, by rfl⟩ : syracuseStep 2953307 = 4429961) B4429961
theorem B1968871 : Blo 1967435 1968871 := bstep (se 1 (by rfl) ⟨1476653, by rfl⟩ : syracuseStep 1968871 = 2953307) B2953307
theorem B2214985 : Blo 1967435 2214985 := bbase (se 2 (by rfl) ⟨830619, by rfl⟩ : syracuseStep 2214985 = 1661239) (by norm_num)
theorem B2953313 : Blo 1967435 2953313 := bstep (se 2 (by rfl) ⟨1107492, by rfl⟩ : syracuseStep 2953313 = 2214985) B2214985
theorem B1968875 : Blo 1967435 1968875 := bstep (se 1 (by rfl) ⟨1476656, by rfl⟩ : syracuseStep 1968875 = 2953313) B2953313
theorem B12615061 : Blo 1967435 12615061 := bbase (se 6 (by rfl) ⟨295665, by rfl⟩ : syracuseStep 12615061 = 591331) (by norm_num)
theorem B16820081 : Blo 1967435 16820081 := bstep (se 2 (by rfl) ⟨6307530, by rfl⟩ : syracuseStep 16820081 = 12615061) B12615061
theorem B11213387 : Blo 1967435 11213387 := bstep (se 1 (by rfl) ⟨8410040, by rfl⟩ : syracuseStep 11213387 = 16820081) B16820081
theorem B7475591 : Blo 1967435 7475591 := bstep (se 1 (by rfl) ⟨5606693, by rfl⟩ : syracuseStep 7475591 = 11213387) B11213387
theorem B4983727 : Blo 1967435 4983727 := bstep (se 1 (by rfl) ⟨3737795, by rfl⟩ : syracuseStep 4983727 = 7475591) B7475591
theorem B6644969 : Blo 1967435 6644969 := bstep (se 2 (by rfl) ⟨2491863, by rfl⟩ : syracuseStep 6644969 = 4983727) B4983727
theorem B4429979 : Blo 1967435 4429979 := bstep (se 1 (by rfl) ⟨3322484, by rfl⟩ : syracuseStep 4429979 = 6644969) B6644969
theorem B2953319 : Blo 1967435 2953319 := bstep (se 1 (by rfl) ⟨2214989, by rfl⟩ : syracuseStep 2953319 = 4429979) B4429979
theorem B1968879 : Blo 1967435 1968879 := bstep (se 1 (by rfl) ⟨1476659, by rfl⟩ : syracuseStep 1968879 = 2953319) B2953319
theorem B2953325 : Blo 1967435 2953325 := bbase (se 3 (by rfl) ⟨553748, by rfl⟩ : syracuseStep 2953325 = 1107497) (by norm_num)
theorem B1968883 : Blo 1967435 1968883 := bstep (se 1 (by rfl) ⟨1476662, by rfl⟩ : syracuseStep 1968883 = 2953325) B2953325
theorem B4429997 : Blo 1967435 4429997 := bbase (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) (by norm_num)
theorem B2953331 : Blo 1967435 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B1968887 : Blo 1967435 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B8980901 : Blo 1967435 8980901 := bbase (se 4 (by rfl) ⟨841959, by rfl⟩ : syracuseStep 8980901 = 1683919) (by norm_num)
theorem B5987267 : Blo 1967435 5987267 := bstep (se 1 (by rfl) ⟨4490450, by rfl⟩ : syracuseStep 5987267 = 8980901) B8980901
theorem B3991511 : Blo 1967435 3991511 := bstep (se 1 (by rfl) ⟨2993633, by rfl⟩ : syracuseStep 3991511 = 5987267) B5987267
theorem B2661007 : Blo 1967435 2661007 := bstep (se 1 (by rfl) ⟨1995755, by rfl⟩ : syracuseStep 2661007 = 3991511) B3991511
theorem B3548009 : Blo 1967435 3548009 := bstep (se 2 (by rfl) ⟨1330503, by rfl⟩ : syracuseStep 3548009 = 2661007) B2661007
theorem B9461357 : Blo 1967435 9461357 := bstep (se 3 (by rfl) ⟨1774004, by rfl⟩ : syracuseStep 9461357 = 3548009) B3548009
theorem B6307571 : Blo 1967435 6307571 := bstep (se 1 (by rfl) ⟨4730678, by rfl⟩ : syracuseStep 6307571 = 9461357) B9461357
theorem B4205047 : Blo 1967435 4205047 := bstep (se 1 (by rfl) ⟨3153785, by rfl⟩ : syracuseStep 4205047 = 6307571) B6307571
theorem B5606729 : Blo 1967435 5606729 := bstep (se 2 (by rfl) ⟨2102523, by rfl⟩ : syracuseStep 5606729 = 4205047) B4205047
theorem B3737819 : Blo 1967435 3737819 := bstep (se 1 (by rfl) ⟨2803364, by rfl⟩ : syracuseStep 3737819 = 5606729) B5606729
theorem B2491879 : Blo 1967435 2491879 := bstep (se 1 (by rfl) ⟨1868909, by rfl⟩ : syracuseStep 2491879 = 3737819) B3737819
theorem B3322505 : Blo 1967435 3322505 := bstep (se 2 (by rfl) ⟨1245939, by rfl⟩ : syracuseStep 3322505 = 2491879) B2491879
theorem B2215003 : Blo 1967435 2215003 := bstep (se 1 (by rfl) ⟨1661252, by rfl⟩ : syracuseStep 2215003 = 3322505) B3322505
theorem B2953337 : Blo 1967435 2953337 := bstep (se 2 (by rfl) ⟨1107501, by rfl⟩ : syracuseStep 2953337 = 2215003) B2215003
theorem B1968891 : Blo 1967435 1968891 := bstep (se 1 (by rfl) ⟨1476668, by rfl⟩ : syracuseStep 1968891 = 2953337) B2953337
theorem B5051765 : Blo 1967435 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B13471373 : Blo 1967435 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B8980915 : Blo 1967435 8980915 := bstep (se 1 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 8980915 = 13471373) B13471373
theorem B11974553 : Blo 1967435 11974553 := bstep (se 2 (by rfl) ⟨4490457, by rfl⟩ : syracuseStep 11974553 = 8980915) B8980915
theorem B7983035 : Blo 1967435 7983035 := bstep (se 1 (by rfl) ⟨5987276, by rfl⟩ : syracuseStep 7983035 = 11974553) B11974553
theorem B5322023 : Blo 1967435 5322023 := bstep (se 1 (by rfl) ⟨3991517, by rfl⟩ : syracuseStep 5322023 = 7983035) B7983035
theorem B3548015 : Blo 1967435 3548015 := bstep (se 1 (by rfl) ⟨2661011, by rfl⟩ : syracuseStep 3548015 = 5322023) B5322023
theorem B2365343 : Blo 1967435 2365343 := bstep (se 1 (by rfl) ⟨1774007, by rfl⟩ : syracuseStep 2365343 = 3548015) B3548015
theorem B25230325 : Blo 1967435 25230325 := bstep (se 5 (by rfl) ⟨1182671, by rfl⟩ : syracuseStep 25230325 = 2365343) B2365343
theorem B33640433 : Blo 1967435 33640433 := bstep (se 2 (by rfl) ⟨12615162, by rfl⟩ : syracuseStep 33640433 = 25230325) B25230325
theorem B22426955 : Blo 1967435 22426955 := bstep (se 1 (by rfl) ⟨16820216, by rfl⟩ : syracuseStep 22426955 = 33640433) B33640433
theorem B14951303 : Blo 1967435 14951303 := bstep (se 1 (by rfl) ⟨11213477, by rfl⟩ : syracuseStep 14951303 = 22426955) B22426955
theorem B9967535 : Blo 1967435 9967535 := bstep (se 1 (by rfl) ⟨7475651, by rfl⟩ : syracuseStep 9967535 = 14951303) B14951303
theorem B6645023 : Blo 1967435 6645023 := bstep (se 1 (by rfl) ⟨4983767, by rfl⟩ : syracuseStep 6645023 = 9967535) B9967535
theorem B4430015 : Blo 1967435 4430015 := bstep (se 1 (by rfl) ⟨3322511, by rfl⟩ : syracuseStep 4430015 = 6645023) B6645023
theorem B2953343 : Blo 1967435 2953343 := bstep (se 1 (by rfl) ⟨2215007, by rfl⟩ : syracuseStep 2953343 = 4430015) B4430015
theorem B1968895 : Blo 1967435 1968895 := bstep (se 1 (by rfl) ⟨1476671, by rfl⟩ : syracuseStep 1968895 = 2953343) B2953343
theorem B2953349 : Blo 1967435 2953349 := bbase (se 4 (by rfl) ⟨276876, by rfl⟩ : syracuseStep 2953349 = 553753) (by norm_num)
theorem B1968899 : Blo 1967435 1968899 := bstep (se 1 (by rfl) ⟨1476674, by rfl⟩ : syracuseStep 1968899 = 2953349) B2953349
theorem B3322525 : Blo 1967435 3322525 := bbase (se 3 (by rfl) ⟨622973, by rfl⟩ : syracuseStep 3322525 = 1245947) (by norm_num)
theorem B4430033 : Blo 1967435 4430033 := bstep (se 2 (by rfl) ⟨1661262, by rfl⟩ : syracuseStep 4430033 = 3322525) B3322525
theorem B2953355 : Blo 1967435 2953355 := bstep (se 1 (by rfl) ⟨2215016, by rfl⟩ : syracuseStep 2953355 = 4430033) B4430033
theorem B1968903 : Blo 1967435 1968903 := bstep (se 1 (by rfl) ⟨1476677, by rfl⟩ : syracuseStep 1968903 = 2953355) B2953355
theorem B2215021 : Blo 1967435 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B2953361 : Blo 1967435 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B1968907 : Blo 1967435 1968907 := bstep (se 1 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 1968907 = 2953361) B2953361
theorem B6645077 : Blo 1967435 6645077 := bbase (se 12 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 6645077 = 4867) (by norm_num)
theorem B4430051 : Blo 1967435 4430051 := bstep (se 1 (by rfl) ⟨3322538, by rfl⟩ : syracuseStep 4430051 = 6645077) B6645077
theorem B2953367 : Blo 1967435 2953367 := bstep (se 1 (by rfl) ⟨2215025, by rfl⟩ : syracuseStep 2953367 = 4430051) B4430051
theorem B1968911 : Blo 1967435 1968911 := bstep (se 1 (by rfl) ⟨1476683, by rfl⟩ : syracuseStep 1968911 = 2953367) B2953367
theorem B2953373 : Blo 1967435 2953373 := bbase (se 3 (by rfl) ⟨553757, by rfl⟩ : syracuseStep 2953373 = 1107515) (by norm_num)
theorem B1968915 : Blo 1967435 1968915 := bstep (se 1 (by rfl) ⟨1476686, by rfl⟩ : syracuseStep 1968915 = 2953373) B2953373
theorem B4430069 : Blo 1967435 4430069 := bbase (se 5 (by rfl) ⟨207659, by rfl⟩ : syracuseStep 4430069 = 415319) (by norm_num)
theorem B2953379 : Blo 1967435 2953379 := bstep (se 1 (by rfl) ⟨2215034, by rfl⟩ : syracuseStep 2953379 = 4430069) B4430069
theorem B1968919 : Blo 1967435 1968919 := bstep (se 1 (by rfl) ⟨1476689, by rfl⟩ : syracuseStep 1968919 = 2953379) B2953379
theorem B5051837 : Blo 1967435 5051837 := bbase (se 3 (by rfl) ⟨947219, by rfl⟩ : syracuseStep 5051837 = 1894439) (by norm_num)
theorem B3367891 : Blo 1967435 3367891 := bstep (se 1 (by rfl) ⟨2525918, by rfl⟩ : syracuseStep 3367891 = 5051837) B5051837
theorem B4490521 : Blo 1967435 4490521 := bstep (se 2 (by rfl) ⟨1683945, by rfl⟩ : syracuseStep 4490521 = 3367891) B3367891
theorem B23949445 : Blo 1967435 23949445 := bstep (se 4 (by rfl) ⟨2245260, by rfl⟩ : syracuseStep 23949445 = 4490521) B4490521
theorem B31932593 : Blo 1967435 31932593 := bstep (se 2 (by rfl) ⟨11974722, by rfl⟩ : syracuseStep 31932593 = 23949445) B23949445
theorem B21288395 : Blo 1967435 21288395 := bstep (se 1 (by rfl) ⟨15966296, by rfl⟩ : syracuseStep 21288395 = 31932593) B31932593
theorem B14192263 : Blo 1967435 14192263 := bstep (se 1 (by rfl) ⟨10644197, by rfl⟩ : syracuseStep 14192263 = 21288395) B21288395
theorem B18923017 : Blo 1967435 18923017 := bstep (se 2 (by rfl) ⟨7096131, by rfl⟩ : syracuseStep 18923017 = 14192263) B14192263
theorem B25230689 : Blo 1967435 25230689 := bstep (se 2 (by rfl) ⟨9461508, by rfl⟩ : syracuseStep 25230689 = 18923017) B18923017
theorem B16820459 : Blo 1967435 16820459 := bstep (se 1 (by rfl) ⟨12615344, by rfl⟩ : syracuseStep 16820459 = 25230689) B25230689
theorem B11213639 : Blo 1967435 11213639 := bstep (se 1 (by rfl) ⟨8410229, by rfl⟩ : syracuseStep 11213639 = 16820459) B16820459
theorem B7475759 : Blo 1967435 7475759 := bstep (se 1 (by rfl) ⟨5606819, by rfl⟩ : syracuseStep 7475759 = 11213639) B11213639
theorem B4983839 : Blo 1967435 4983839 := bstep (se 1 (by rfl) ⟨3737879, by rfl⟩ : syracuseStep 4983839 = 7475759) B7475759
theorem B3322559 : Blo 1967435 3322559 := bstep (se 1 (by rfl) ⟨2491919, by rfl⟩ : syracuseStep 3322559 = 4983839) B4983839
theorem B2215039 : Blo 1967435 2215039 := bstep (se 1 (by rfl) ⟨1661279, by rfl⟩ : syracuseStep 2215039 = 3322559) B3322559
theorem B2953385 : Blo 1967435 2953385 := bstep (se 2 (by rfl) ⟨1107519, by rfl⟩ : syracuseStep 2953385 = 2215039) B2215039
theorem B1968923 : Blo 1967435 1968923 := bstep (se 1 (by rfl) ⟨1476692, by rfl⟩ : syracuseStep 1968923 = 2953385) B2953385
theorem B6307685 : Blo 1967435 6307685 := bbase (se 4 (by rfl) ⟨591345, by rfl⟩ : syracuseStep 6307685 = 1182691) (by norm_num)
theorem B4205123 : Blo 1967435 4205123 := bstep (se 1 (by rfl) ⟨3153842, by rfl⟩ : syracuseStep 4205123 = 6307685) B6307685
theorem B2803415 : Blo 1967435 2803415 := bstep (se 1 (by rfl) ⟨2102561, by rfl⟩ : syracuseStep 2803415 = 4205123) B4205123
theorem B7475773 : Blo 1967435 7475773 := bstep (se 3 (by rfl) ⟨1401707, by rfl⟩ : syracuseStep 7475773 = 2803415) B2803415
theorem B9967697 : Blo 1967435 9967697 := bstep (se 2 (by rfl) ⟨3737886, by rfl⟩ : syracuseStep 9967697 = 7475773) B7475773
theorem B6645131 : Blo 1967435 6645131 := bstep (se 1 (by rfl) ⟨4983848, by rfl⟩ : syracuseStep 6645131 = 9967697) B9967697
theorem B4430087 : Blo 1967435 4430087 := bstep (se 1 (by rfl) ⟨3322565, by rfl⟩ : syracuseStep 4430087 = 6645131) B6645131
theorem B2953391 : Blo 1967435 2953391 := bstep (se 1 (by rfl) ⟨2215043, by rfl⟩ : syracuseStep 2953391 = 4430087) B4430087
theorem B1968927 : Blo 1967435 1968927 := bstep (se 1 (by rfl) ⟨1476695, by rfl⟩ : syracuseStep 1968927 = 2953391) B2953391
theorem B2953397 : Blo 1967435 2953397 := bbase (se 5 (by rfl) ⟨138440, by rfl⟩ : syracuseStep 2953397 = 276881) (by norm_num)
theorem B1968931 : Blo 1967435 1968931 := bstep (se 1 (by rfl) ⟨1476698, by rfl⟩ : syracuseStep 1968931 = 2953397) B2953397
theorem B4983869 : Blo 1967435 4983869 := bbase (se 3 (by rfl) ⟨934475, by rfl⟩ : syracuseStep 4983869 = 1868951) (by norm_num)
theorem B3322579 : Blo 1967435 3322579 := bstep (se 1 (by rfl) ⟨2491934, by rfl⟩ : syracuseStep 3322579 = 4983869) B4983869
theorem B4430105 : Blo 1967435 4430105 := bstep (se 2 (by rfl) ⟨1661289, by rfl⟩ : syracuseStep 4430105 = 3322579) B3322579
theorem B2953403 : Blo 1967435 2953403 := bstep (se 1 (by rfl) ⟨2215052, by rfl⟩ : syracuseStep 2953403 = 4430105) B4430105
theorem B1968935 : Blo 1967435 1968935 := bstep (se 1 (by rfl) ⟨1476701, by rfl⟩ : syracuseStep 1968935 = 2953403) B2953403
theorem B2215057 : Blo 1967435 2215057 := bbase (se 2 (by rfl) ⟨830646, by rfl⟩ : syracuseStep 2215057 = 1661293) (by norm_num)
theorem B2953409 : Blo 1967435 2953409 := bstep (se 2 (by rfl) ⟨1107528, by rfl⟩ : syracuseStep 2953409 = 2215057) B2215057
theorem B1968939 : Blo 1967435 1968939 := bstep (se 1 (by rfl) ⟨1476704, by rfl⟩ : syracuseStep 1968939 = 2953409) B2953409
theorem B3737917 : Blo 1967435 3737917 := bbase (se 3 (by rfl) ⟨700859, by rfl⟩ : syracuseStep 3737917 = 1401719) (by norm_num)
theorem B4983889 : Blo 1967435 4983889 := bstep (se 2 (by rfl) ⟨1868958, by rfl⟩ : syracuseStep 4983889 = 3737917) B3737917
theorem B6645185 : Blo 1967435 6645185 := bstep (se 2 (by rfl) ⟨2491944, by rfl⟩ : syracuseStep 6645185 = 4983889) B4983889
theorem B4430123 : Blo 1967435 4430123 := bstep (se 1 (by rfl) ⟨3322592, by rfl⟩ : syracuseStep 4430123 = 6645185) B6645185
theorem B2953415 : Blo 1967435 2953415 := bstep (se 1 (by rfl) ⟨2215061, by rfl⟩ : syracuseStep 2953415 = 4430123) B4430123
theorem B1968943 : Blo 1967435 1968943 := bstep (se 1 (by rfl) ⟨1476707, by rfl⟩ : syracuseStep 1968943 = 2953415) B2953415
theorem B2953421 : Blo 1967435 2953421 := bbase (se 3 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 2953421 = 1107533) (by norm_num)
theorem B1968947 : Blo 1967435 1968947 := bstep (se 1 (by rfl) ⟨1476710, by rfl⟩ : syracuseStep 1968947 = 2953421) B2953421
theorem B4430141 : Blo 1967435 4430141 := bbase (se 3 (by rfl) ⟨830651, by rfl⟩ : syracuseStep 4430141 = 1661303) (by norm_num)
theorem B2953427 : Blo 1967435 2953427 := bstep (se 1 (by rfl) ⟨2215070, by rfl⟩ : syracuseStep 2953427 = 4430141) B4430141
theorem B1968951 : Blo 1967435 1968951 := bstep (se 1 (by rfl) ⟨1476713, by rfl⟩ : syracuseStep 1968951 = 2953427) B2953427
theorem B3322613 : Blo 1967435 3322613 := bbase (se 5 (by rfl) ⟨155747, by rfl⟩ : syracuseStep 3322613 = 311495) (by norm_num)
theorem B2215075 : Blo 1967435 2215075 := bstep (se 1 (by rfl) ⟨1661306, by rfl⟩ : syracuseStep 2215075 = 3322613) B3322613
theorem B2953433 : Blo 1967435 2953433 := bstep (se 2 (by rfl) ⟨1107537, by rfl⟩ : syracuseStep 2953433 = 2215075) B2215075
theorem B1968955 : Blo 1967435 1968955 := bstep (se 1 (by rfl) ⟨1476716, by rfl⟩ : syracuseStep 1968955 = 2953433) B2953433
theorem B7096261 : Blo 1967435 7096261 := bbase (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) (by norm_num)
theorem B9461681 : Blo 1967435 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B6307787 : Blo 1967435 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B4205191 : Blo 1967435 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B5606921 : Blo 1967435 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B14951789 : Blo 1967435 14951789 := bstep (se 3 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 14951789 = 5606921) B5606921
theorem B9967859 : Blo 1967435 9967859 := bstep (se 1 (by rfl) ⟨7475894, by rfl⟩ : syracuseStep 9967859 = 14951789) B14951789
theorem B6645239 : Blo 1967435 6645239 := bstep (se 1 (by rfl) ⟨4983929, by rfl⟩ : syracuseStep 6645239 = 9967859) B9967859
theorem B4430159 : Blo 1967435 4430159 := bstep (se 1 (by rfl) ⟨3322619, by rfl⟩ : syracuseStep 4430159 = 6645239) B6645239
theorem B2953439 : Blo 1967435 2953439 := bstep (se 1 (by rfl) ⟨2215079, by rfl⟩ : syracuseStep 2953439 = 4430159) B4430159
theorem B1968959 : Blo 1967435 1968959 := bstep (se 1 (by rfl) ⟨1476719, by rfl⟩ : syracuseStep 1968959 = 2953439) B2953439
theorem B2953445 : Blo 1967435 2953445 := bbase (se 4 (by rfl) ⟨276885, by rfl⟩ : syracuseStep 2953445 = 553771) (by norm_num)
theorem B1968963 : Blo 1967435 1968963 := bstep (se 1 (by rfl) ⟨1476722, by rfl⟩ : syracuseStep 1968963 = 2953445) B2953445
theorem B4730861 : Blo 1967435 4730861 := bbase (se 3 (by rfl) ⟨887036, by rfl⟩ : syracuseStep 4730861 = 1774073) (by norm_num)
theorem B3153907 : Blo 1967435 3153907 := bstep (se 1 (by rfl) ⟨2365430, by rfl⟩ : syracuseStep 3153907 = 4730861) B4730861
theorem B4205209 : Blo 1967435 4205209 := bstep (se 2 (by rfl) ⟨1576953, by rfl⟩ : syracuseStep 4205209 = 3153907) B3153907
theorem B5606945 : Blo 1967435 5606945 := bstep (se 2 (by rfl) ⟨2102604, by rfl⟩ : syracuseStep 5606945 = 4205209) B4205209
theorem B3737963 : Blo 1967435 3737963 := bstep (se 1 (by rfl) ⟨2803472, by rfl⟩ : syracuseStep 3737963 = 5606945) B5606945
theorem B2491975 : Blo 1967435 2491975 := bstep (se 1 (by rfl) ⟨1868981, by rfl⟩ : syracuseStep 2491975 = 3737963) B3737963
theorem B3322633 : Blo 1967435 3322633 := bstep (se 2 (by rfl) ⟨1245987, by rfl⟩ : syracuseStep 3322633 = 2491975) B2491975
theorem B4430177 : Blo 1967435 4430177 := bstep (se 2 (by rfl) ⟨1661316, by rfl⟩ : syracuseStep 4430177 = 3322633) B3322633
theorem B2953451 : Blo 1967435 2953451 := bstep (se 1 (by rfl) ⟨2215088, by rfl⟩ : syracuseStep 2953451 = 4430177) B4430177
theorem B1968967 : Blo 1967435 1968967 := bstep (se 1 (by rfl) ⟨1476725, by rfl⟩ : syracuseStep 1968967 = 2953451) B2953451
theorem B2215093 : Blo 1967435 2215093 := bbase (se 5 (by rfl) ⟨103832, by rfl⟩ : syracuseStep 2215093 = 207665) (by norm_num)
theorem B2953457 : Blo 1967435 2953457 := bstep (se 2 (by rfl) ⟨1107546, by rfl⟩ : syracuseStep 2953457 = 2215093) B2215093
theorem B1968971 : Blo 1967435 1968971 := bstep (se 1 (by rfl) ⟨1476728, by rfl⟩ : syracuseStep 1968971 = 2953457) B2953457
theorem B2491985 : Blo 1967435 2491985 := bbase (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) (by norm_num)
theorem B6645293 : Blo 1967435 6645293 := bstep (se 3 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 6645293 = 2491985) B2491985
theorem B4430195 : Blo 1967435 4430195 := bstep (se 1 (by rfl) ⟨3322646, by rfl⟩ : syracuseStep 4430195 = 6645293) B6645293
theorem B2953463 : Blo 1967435 2953463 := bstep (se 1 (by rfl) ⟨2215097, by rfl⟩ : syracuseStep 2953463 = 4430195) B4430195
theorem B1968975 : Blo 1967435 1968975 := bstep (se 1 (by rfl) ⟨1476731, by rfl⟩ : syracuseStep 1968975 = 2953463) B2953463
theorem B2953469 : Blo 1967435 2953469 := bbase (se 3 (by rfl) ⟨553775, by rfl⟩ : syracuseStep 2953469 = 1107551) (by norm_num)
theorem B1968979 : Blo 1967435 1968979 := bstep (se 1 (by rfl) ⟨1476734, by rfl⟩ : syracuseStep 1968979 = 2953469) B2953469
theorem B4430213 : Blo 1967435 4430213 := bbase (se 4 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 4430213 = 830665) (by norm_num)
theorem B2953475 : Blo 1967435 2953475 := bstep (se 1 (by rfl) ⟨2215106, by rfl⟩ : syracuseStep 2953475 = 4430213) B4430213
theorem B1968983 : Blo 1967435 1968983 := bstep (se 1 (by rfl) ⟨1476737, by rfl⟩ : syracuseStep 1968983 = 2953475) B2953475
theorem B2803501 : Blo 1967435 2803501 := bbase (se 3 (by rfl) ⟨525656, by rfl⟩ : syracuseStep 2803501 = 1051313) (by norm_num)
theorem B3738001 : Blo 1967435 3738001 := bstep (se 2 (by rfl) ⟨1401750, by rfl⟩ : syracuseStep 3738001 = 2803501) B2803501
theorem B4984001 : Blo 1967435 4984001 := bstep (se 2 (by rfl) ⟨1869000, by rfl⟩ : syracuseStep 4984001 = 3738001) B3738001
theorem B3322667 : Blo 1967435 3322667 := bstep (se 1 (by rfl) ⟨2492000, by rfl⟩ : syracuseStep 3322667 = 4984001) B4984001
theorem B2215111 : Blo 1967435 2215111 := bstep (se 1 (by rfl) ⟨1661333, by rfl⟩ : syracuseStep 2215111 = 3322667) B3322667
theorem B2953481 : Blo 1967435 2953481 := bstep (se 2 (by rfl) ⟨1107555, by rfl⟩ : syracuseStep 2953481 = 2215111) B2215111
theorem B1968987 : Blo 1967435 1968987 := bstep (se 1 (by rfl) ⟨1476740, by rfl⟩ : syracuseStep 1968987 = 2953481) B2953481
theorem B9968021 : Blo 1967435 9968021 := bbase (se 6 (by rfl) ⟨233625, by rfl⟩ : syracuseStep 9968021 = 467251) (by norm_num)
theorem B6645347 : Blo 1967435 6645347 := bstep (se 1 (by rfl) ⟨4984010, by rfl⟩ : syracuseStep 6645347 = 9968021) B9968021
theorem B4430231 : Blo 1967435 4430231 := bstep (se 1 (by rfl) ⟨3322673, by rfl⟩ : syracuseStep 4430231 = 6645347) B6645347
theorem B2953487 : Blo 1967435 2953487 := bstep (se 1 (by rfl) ⟨2215115, by rfl⟩ : syracuseStep 2953487 = 4430231) B4430231
theorem B1968991 : Blo 1967435 1968991 := bstep (se 1 (by rfl) ⟨1476743, by rfl⟩ : syracuseStep 1968991 = 2953487) B2953487
theorem B2953493 : Blo 1967435 2953493 := bbase (se 6 (by rfl) ⟨69222, by rfl⟩ : syracuseStep 2953493 = 138445) (by norm_num)
theorem B1968995 : Blo 1967435 1968995 := bstep (se 1 (by rfl) ⟨1476746, by rfl⟩ : syracuseStep 1968995 = 2953493) B2953493
theorem B7096405 : Blo 1967435 7096405 := bbase (se 8 (by rfl) ⟨41580, by rfl⟩ : syracuseStep 7096405 = 83161) (by norm_num)
theorem B9461873 : Blo 1967435 9461873 := bstep (se 2 (by rfl) ⟨3548202, by rfl⟩ : syracuseStep 9461873 = 7096405) B7096405
theorem B25231661 : Blo 1967435 25231661 := bstep (se 3 (by rfl) ⟨4730936, by rfl⟩ : syracuseStep 25231661 = 9461873) B9461873
theorem B16821107 : Blo 1967435 16821107 := bstep (se 1 (by rfl) ⟨12615830, by rfl⟩ : syracuseStep 16821107 = 25231661) B25231661
theorem B11214071 : Blo 1967435 11214071 := bstep (se 1 (by rfl) ⟨8410553, by rfl⟩ : syracuseStep 11214071 = 16821107) B16821107
theorem B7476047 : Blo 1967435 7476047 := bstep (se 1 (by rfl) ⟨5607035, by rfl⟩ : syracuseStep 7476047 = 11214071) B11214071
theorem B4984031 : Blo 1967435 4984031 := bstep (se 1 (by rfl) ⟨3738023, by rfl⟩ : syracuseStep 4984031 = 7476047) B7476047
theorem B3322687 : Blo 1967435 3322687 := bstep (se 1 (by rfl) ⟨2492015, by rfl⟩ : syracuseStep 3322687 = 4984031) B4984031
theorem B4430249 : Blo 1967435 4430249 := bstep (se 2 (by rfl) ⟨1661343, by rfl⟩ : syracuseStep 4430249 = 3322687) B3322687
theorem B2953499 : Blo 1967435 2953499 := bstep (se 1 (by rfl) ⟨2215124, by rfl⟩ : syracuseStep 2953499 = 4430249) B4430249
theorem B1968999 : Blo 1967435 1968999 := bstep (se 1 (by rfl) ⟨1476749, by rfl⟩ : syracuseStep 1968999 = 2953499) B2953499
theorem B2215129 : Blo 1967435 2215129 := bbase (se 2 (by rfl) ⟨830673, by rfl⟩ : syracuseStep 2215129 = 1661347) (by norm_num)
theorem B2953505 : Blo 1967435 2953505 := bstep (se 2 (by rfl) ⟨1107564, by rfl⟩ : syracuseStep 2953505 = 2215129) B2215129
theorem B1969003 : Blo 1967435 1969003 := bstep (se 1 (by rfl) ⟨1476752, by rfl⟩ : syracuseStep 1969003 = 2953505) B2953505
theorem B4730957 : Blo 1967435 4730957 := bbase (se 3 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 4730957 = 1774109) (by norm_num)
theorem B3153971 : Blo 1967435 3153971 := bstep (se 1 (by rfl) ⟨2365478, by rfl⟩ : syracuseStep 3153971 = 4730957) B4730957
theorem B2102647 : Blo 1967435 2102647 := bstep (se 1 (by rfl) ⟨1576985, by rfl⟩ : syracuseStep 2102647 = 3153971) B3153971
theorem B2803529 : Blo 1967435 2803529 := bstep (se 2 (by rfl) ⟨1051323, by rfl⟩ : syracuseStep 2803529 = 2102647) B2102647
theorem B7476077 : Blo 1967435 7476077 := bstep (se 3 (by rfl) ⟨1401764, by rfl⟩ : syracuseStep 7476077 = 2803529) B2803529
theorem B4984051 : Blo 1967435 4984051 := bstep (se 1 (by rfl) ⟨3738038, by rfl⟩ : syracuseStep 4984051 = 7476077) B7476077
theorem B6645401 : Blo 1967435 6645401 := bstep (se 2 (by rfl) ⟨2492025, by rfl⟩ : syracuseStep 6645401 = 4984051) B4984051
theorem B4430267 : Blo 1967435 4430267 := bstep (se 1 (by rfl) ⟨3322700, by rfl⟩ : syracuseStep 4430267 = 6645401) B6645401
theorem B2953511 : Blo 1967435 2953511 := bstep (se 1 (by rfl) ⟨2215133, by rfl⟩ : syracuseStep 2953511 = 4430267) B4430267
theorem B1969007 : Blo 1967435 1969007 := bstep (se 1 (by rfl) ⟨1476755, by rfl⟩ : syracuseStep 1969007 = 2953511) B2953511
theorem B2953517 : Blo 1967435 2953517 := bbase (se 3 (by rfl) ⟨553784, by rfl⟩ : syracuseStep 2953517 = 1107569) (by norm_num)
theorem B1969011 : Blo 1967435 1969011 := bstep (se 1 (by rfl) ⟨1476758, by rfl⟩ : syracuseStep 1969011 = 2953517) B2953517
theorem B4430285 : Blo 1967435 4430285 := bbase (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) (by norm_num)
theorem B2953523 : Blo 1967435 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1969015 : Blo 1967435 1969015 := bstep (se 1 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 1969015 = 2953523) B2953523
theorem B2492041 : Blo 1967435 2492041 := bbase (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) (by norm_num)
theorem B3322721 : Blo 1967435 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2215147 : Blo 1967435 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B2953529 : Blo 1967435 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B1969019 : Blo 1967435 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B13472245 : Blo 1967435 13472245 := bbase (se 5 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 13472245 = 1263023) (by norm_num)
theorem B17962993 : Blo 1967435 17962993 := bstep (se 2 (by rfl) ⟨6736122, by rfl⟩ : syracuseStep 17962993 = 13472245) B13472245
theorem B23950657 : Blo 1967435 23950657 := bstep (se 2 (by rfl) ⟨8981496, by rfl⟩ : syracuseStep 23950657 = 17962993) B17962993
theorem B31934209 : Blo 1967435 31934209 := bstep (se 2 (by rfl) ⟨11975328, by rfl⟩ : syracuseStep 31934209 = 23950657) B23950657
theorem B42578945 : Blo 1967435 42578945 := bstep (se 2 (by rfl) ⟨15967104, by rfl⟩ : syracuseStep 42578945 = 31934209) B31934209
theorem B28385963 : Blo 1967435 28385963 := bstep (se 1 (by rfl) ⟨21289472, by rfl⟩ : syracuseStep 28385963 = 42578945) B42578945
theorem B18923975 : Blo 1967435 18923975 := bstep (se 1 (by rfl) ⟨14192981, by rfl⟩ : syracuseStep 18923975 = 28385963) B28385963
theorem B12615983 : Blo 1967435 12615983 := bstep (se 1 (by rfl) ⟨9461987, by rfl⟩ : syracuseStep 12615983 = 18923975) B18923975
theorem B8410655 : Blo 1967435 8410655 := bstep (se 1 (by rfl) ⟨6307991, by rfl⟩ : syracuseStep 8410655 = 12615983) B12615983
theorem B22428413 : Blo 1967435 22428413 := bstep (se 3 (by rfl) ⟨4205327, by rfl⟩ : syracuseStep 22428413 = 8410655) B8410655
theorem B14952275 : Blo 1967435 14952275 := bstep (se 1 (by rfl) ⟨11214206, by rfl⟩ : syracuseStep 14952275 = 22428413) B22428413
theorem B9968183 : Blo 1967435 9968183 := bstep (se 1 (by rfl) ⟨7476137, by rfl⟩ : syracuseStep 9968183 = 14952275) B14952275
theorem B6645455 : Blo 1967435 6645455 := bstep (se 1 (by rfl) ⟨4984091, by rfl⟩ : syracuseStep 6645455 = 9968183) B9968183
theorem B4430303 : Blo 1967435 4430303 := bstep (se 1 (by rfl) ⟨3322727, by rfl⟩ : syracuseStep 4430303 = 6645455) B6645455
theorem B2953535 : Blo 1967435 2953535 := bstep (se 1 (by rfl) ⟨2215151, by rfl⟩ : syracuseStep 2953535 = 4430303) B4430303
theorem B1969023 : Blo 1967435 1969023 := bstep (se 1 (by rfl) ⟨1476767, by rfl⟩ : syracuseStep 1969023 = 2953535) B2953535
theorem B2953541 : Blo 1967435 2953541 := bbase (se 4 (by rfl) ⟨276894, by rfl⟩ : syracuseStep 2953541 = 553789) (by norm_num)
theorem B1969027 : Blo 1967435 1969027 := bstep (se 1 (by rfl) ⟨1476770, by rfl⟩ : syracuseStep 1969027 = 2953541) B2953541
theorem B3322741 : Blo 1967435 3322741 := bbase (se 5 (by rfl) ⟨155753, by rfl⟩ : syracuseStep 3322741 = 311507) (by norm_num)
theorem B4430321 : Blo 1967435 4430321 := bstep (se 2 (by rfl) ⟨1661370, by rfl⟩ : syracuseStep 4430321 = 3322741) B3322741
theorem B2953547 : Blo 1967435 2953547 := bstep (se 1 (by rfl) ⟨2215160, by rfl⟩ : syracuseStep 2953547 = 4430321) B4430321
theorem B1969031 : Blo 1967435 1969031 := bstep (se 1 (by rfl) ⟨1476773, by rfl⟩ : syracuseStep 1969031 = 2953547) B2953547
theorem B2215165 : Blo 1967435 2215165 := bbase (se 3 (by rfl) ⟨415343, by rfl⟩ : syracuseStep 2215165 = 830687) (by norm_num)
theorem B2953553 : Blo 1967435 2953553 := bstep (se 2 (by rfl) ⟨1107582, by rfl⟩ : syracuseStep 2953553 = 2215165) B2215165
theorem B1969035 : Blo 1967435 1969035 := bstep (se 1 (by rfl) ⟨1476776, by rfl⟩ : syracuseStep 1969035 = 2953553) B2953553
theorem B6645509 : Blo 1967435 6645509 := bbase (se 4 (by rfl) ⟨623016, by rfl⟩ : syracuseStep 6645509 = 1246033) (by norm_num)
theorem B4430339 : Blo 1967435 4430339 := bstep (se 1 (by rfl) ⟨3322754, by rfl⟩ : syracuseStep 4430339 = 6645509) B6645509
theorem B2953559 : Blo 1967435 2953559 := bstep (se 1 (by rfl) ⟨2215169, by rfl⟩ : syracuseStep 2953559 = 4430339) B4430339
theorem B1969039 : Blo 1967435 1969039 := bstep (se 1 (by rfl) ⟨1476779, by rfl⟩ : syracuseStep 1969039 = 2953559) B2953559
theorem B2953565 : Blo 1967435 2953565 := bbase (se 3 (by rfl) ⟨553793, by rfl⟩ : syracuseStep 2953565 = 1107587) (by norm_num)
theorem B1969043 : Blo 1967435 1969043 := bstep (se 1 (by rfl) ⟨1476782, by rfl⟩ : syracuseStep 1969043 = 2953565) B2953565
theorem B4430357 : Blo 1967435 4430357 := bbase (se 6 (by rfl) ⟨103836, by rfl⟩ : syracuseStep 4430357 = 207673) (by norm_num)
theorem B2953571 : Blo 1967435 2953571 := bstep (se 1 (by rfl) ⟨2215178, by rfl⟩ : syracuseStep 2953571 = 4430357) B4430357
theorem B1969047 : Blo 1967435 1969047 := bstep (se 1 (by rfl) ⟨1476785, by rfl⟩ : syracuseStep 1969047 = 2953571) B2953571
theorem B7476245 : Blo 1967435 7476245 := bbase (se 6 (by rfl) ⟨175224, by rfl⟩ : syracuseStep 7476245 = 350449) (by norm_num)
theorem B4984163 : Blo 1967435 4984163 := bstep (se 1 (by rfl) ⟨3738122, by rfl⟩ : syracuseStep 4984163 = 7476245) B7476245
theorem B3322775 : Blo 1967435 3322775 := bstep (se 1 (by rfl) ⟨2492081, by rfl⟩ : syracuseStep 3322775 = 4984163) B4984163
theorem B2215183 : Blo 1967435 2215183 := bstep (se 1 (by rfl) ⟨1661387, by rfl⟩ : syracuseStep 2215183 = 3322775) B3322775
theorem B2953577 : Blo 1967435 2953577 := bstep (se 2 (by rfl) ⟨1107591, by rfl⟩ : syracuseStep 2953577 = 2215183) B2215183
theorem B1969051 : Blo 1967435 1969051 := bstep (se 1 (by rfl) ⟨1476788, by rfl⟩ : syracuseStep 1969051 = 2953577) B2953577
theorem B11214389 : Blo 1967435 11214389 := bbase (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) (by norm_num)
theorem B7476259 : Blo 1967435 7476259 := bstep (se 1 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 7476259 = 11214389) B11214389
theorem B9968345 : Blo 1967435 9968345 := bstep (se 2 (by rfl) ⟨3738129, by rfl⟩ : syracuseStep 9968345 = 7476259) B7476259
theorem B6645563 : Blo 1967435 6645563 := bstep (se 1 (by rfl) ⟨4984172, by rfl⟩ : syracuseStep 6645563 = 9968345) B9968345
theorem B4430375 : Blo 1967435 4430375 := bstep (se 1 (by rfl) ⟨3322781, by rfl⟩ : syracuseStep 4430375 = 6645563) B6645563
theorem B2953583 : Blo 1967435 2953583 := bstep (se 1 (by rfl) ⟨2215187, by rfl⟩ : syracuseStep 2953583 = 4430375) B4430375
theorem B1969055 : Blo 1967435 1969055 := bstep (se 1 (by rfl) ⟨1476791, by rfl⟩ : syracuseStep 1969055 = 2953583) B2953583
theorem B2953589 : Blo 1967435 2953589 := bbase (se 5 (by rfl) ⟨138449, by rfl⟩ : syracuseStep 2953589 = 276899) (by norm_num)
theorem B1969059 : Blo 1967435 1969059 := bstep (se 1 (by rfl) ⟨1476794, by rfl⟩ : syracuseStep 1969059 = 2953589) B2953589
theorem B3154061 : Blo 1967435 3154061 := bbase (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) (by norm_num)
theorem B2102707 : Blo 1967435 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B2803609 : Blo 1967435 2803609 := bstep (se 2 (by rfl) ⟨1051353, by rfl⟩ : syracuseStep 2803609 = 2102707) B2102707
theorem B3738145 : Blo 1967435 3738145 := bstep (se 2 (by rfl) ⟨1401804, by rfl⟩ : syracuseStep 3738145 = 2803609) B2803609
theorem B4984193 : Blo 1967435 4984193 := bstep (se 2 (by rfl) ⟨1869072, by rfl⟩ : syracuseStep 4984193 = 3738145) B3738145
theorem B3322795 : Blo 1967435 3322795 := bstep (se 1 (by rfl) ⟨2492096, by rfl⟩ : syracuseStep 3322795 = 4984193) B4984193
theorem B4430393 : Blo 1967435 4430393 := bstep (se 2 (by rfl) ⟨1661397, by rfl⟩ : syracuseStep 4430393 = 3322795) B3322795
theorem B2953595 : Blo 1967435 2953595 := bstep (se 1 (by rfl) ⟨2215196, by rfl⟩ : syracuseStep 2953595 = 4430393) B4430393
theorem B1969063 : Blo 1967435 1969063 := bstep (se 1 (by rfl) ⟨1476797, by rfl⟩ : syracuseStep 1969063 = 2953595) B2953595
theorem B2215201 : Blo 1967435 2215201 := bbase (se 2 (by rfl) ⟨830700, by rfl⟩ : syracuseStep 2215201 = 1661401) (by norm_num)
theorem B2953601 : Blo 1967435 2953601 := bstep (se 2 (by rfl) ⟨1107600, by rfl⟩ : syracuseStep 2953601 = 2215201) B2215201
theorem B1969067 : Blo 1967435 1969067 := bstep (se 1 (by rfl) ⟨1476800, by rfl⟩ : syracuseStep 1969067 = 2953601) B2953601
theorem B4984213 : Blo 1967435 4984213 := bbase (se 6 (by rfl) ⟨116817, by rfl⟩ : syracuseStep 4984213 = 233635) (by norm_num)
theorem B6645617 : Blo 1967435 6645617 := bstep (se 2 (by rfl) ⟨2492106, by rfl⟩ : syracuseStep 6645617 = 4984213) B4984213
theorem B4430411 : Blo 1967435 4430411 := bstep (se 1 (by rfl) ⟨3322808, by rfl⟩ : syracuseStep 4430411 = 6645617) B6645617
theorem B2953607 : Blo 1967435 2953607 := bstep (se 1 (by rfl) ⟨2215205, by rfl⟩ : syracuseStep 2953607 = 4430411) B4430411
theorem B1969071 : Blo 1967435 1969071 := bstep (se 1 (by rfl) ⟨1476803, by rfl⟩ : syracuseStep 1969071 = 2953607) B2953607
theorem B2953613 : Blo 1967435 2953613 := bbase (se 3 (by rfl) ⟨553802, by rfl⟩ : syracuseStep 2953613 = 1107605) (by norm_num)
theorem B1969075 : Blo 1967435 1969075 := bstep (se 1 (by rfl) ⟨1476806, by rfl⟩ : syracuseStep 1969075 = 2953613) B2953613
theorem B4430429 : Blo 1967435 4430429 := bbase (se 3 (by rfl) ⟨830705, by rfl⟩ : syracuseStep 4430429 = 1661411) (by norm_num)
theorem B2953619 : Blo 1967435 2953619 := bstep (se 1 (by rfl) ⟨2215214, by rfl⟩ : syracuseStep 2953619 = 4430429) B4430429
theorem B1969079 : Blo 1967435 1969079 := bstep (se 1 (by rfl) ⟨1476809, by rfl⟩ : syracuseStep 1969079 = 2953619) B2953619
theorem B3322829 : Blo 1967435 3322829 := bbase (se 3 (by rfl) ⟨623030, by rfl⟩ : syracuseStep 3322829 = 1246061) (by norm_num)
theorem B2215219 : Blo 1967435 2215219 := bstep (se 1 (by rfl) ⟨1661414, by rfl⟩ : syracuseStep 2215219 = 3322829) B3322829
theorem B2953625 : Blo 1967435 2953625 := bstep (se 2 (by rfl) ⟨1107609, by rfl⟩ : syracuseStep 2953625 = 2215219) B2215219
theorem B1969083 : Blo 1967435 1969083 := bstep (se 1 (by rfl) ⟨1476812, by rfl⟩ : syracuseStep 1969083 = 2953625) B2953625
theorem B1995953 : Blo 1967435 1995953 := bbase (se 2 (by rfl) ⟨748482, by rfl⟩ : syracuseStep 1995953 = 1496965) (by norm_num)
theorem B21290165 : Blo 1967435 21290165 := bstep (se 5 (by rfl) ⟨997976, by rfl⟩ : syracuseStep 21290165 = 1995953) B1995953
theorem B14193443 : Blo 1967435 14193443 := bstep (se 1 (by rfl) ⟨10645082, by rfl⟩ : syracuseStep 14193443 = 21290165) B21290165
theorem B9462295 : Blo 1967435 9462295 := bstep (se 1 (by rfl) ⟨7096721, by rfl⟩ : syracuseStep 9462295 = 14193443) B14193443
theorem B12616393 : Blo 1967435 12616393 := bstep (se 2 (by rfl) ⟨4731147, by rfl⟩ : syracuseStep 12616393 = 9462295) B9462295
theorem B16821857 : Blo 1967435 16821857 := bstep (se 2 (by rfl) ⟨6308196, by rfl⟩ : syracuseStep 16821857 = 12616393) B12616393
theorem B11214571 : Blo 1967435 11214571 := bstep (se 1 (by rfl) ⟨8410928, by rfl⟩ : syracuseStep 11214571 = 16821857) B16821857
theorem B14952761 : Blo 1967435 14952761 := bstep (se 2 (by rfl) ⟨5607285, by rfl⟩ : syracuseStep 14952761 = 11214571) B11214571
theorem B9968507 : Blo 1967435 9968507 := bstep (se 1 (by rfl) ⟨7476380, by rfl⟩ : syracuseStep 9968507 = 14952761) B14952761
theorem B6645671 : Blo 1967435 6645671 := bstep (se 1 (by rfl) ⟨4984253, by rfl⟩ : syracuseStep 6645671 = 9968507) B9968507
theorem B4430447 : Blo 1967435 4430447 := bstep (se 1 (by rfl) ⟨3322835, by rfl⟩ : syracuseStep 4430447 = 6645671) B6645671
theorem B2953631 : Blo 1967435 2953631 := bstep (se 1 (by rfl) ⟨2215223, by rfl⟩ : syracuseStep 2953631 = 4430447) B4430447
theorem B1969087 : Blo 1967435 1969087 := bstep (se 1 (by rfl) ⟨1476815, by rfl⟩ : syracuseStep 1969087 = 2953631) B2953631
theorem B2953637 : Blo 1967435 2953637 := bbase (se 4 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 2953637 = 553807) (by norm_num)
theorem B1969091 : Blo 1967435 1969091 := bstep (se 1 (by rfl) ⟨1476818, by rfl⟩ : syracuseStep 1969091 = 2953637) B2953637
theorem B2492137 : Blo 1967435 2492137 := bbase (se 2 (by rfl) ⟨934551, by rfl⟩ : syracuseStep 2492137 = 1869103) (by norm_num)
theorem B3322849 : Blo 1967435 3322849 := bstep (se 2 (by rfl) ⟨1246068, by rfl⟩ : syracuseStep 3322849 = 2492137) B2492137
theorem B4430465 : Blo 1967435 4430465 := bstep (se 2 (by rfl) ⟨1661424, by rfl⟩ : syracuseStep 4430465 = 3322849) B3322849
theorem B2953643 : Blo 1967435 2953643 := bstep (se 1 (by rfl) ⟨2215232, by rfl⟩ : syracuseStep 2953643 = 4430465) B4430465
theorem B1969095 : Blo 1967435 1969095 := bstep (se 1 (by rfl) ⟨1476821, by rfl⟩ : syracuseStep 1969095 = 2953643) B2953643
theorem B2215237 : Blo 1967435 2215237 := bbase (se 4 (by rfl) ⟨207678, by rfl⟩ : syracuseStep 2215237 = 415357) (by norm_num)
theorem B2953649 : Blo 1967435 2953649 := bstep (se 2 (by rfl) ⟨1107618, by rfl⟩ : syracuseStep 2953649 = 2215237) B2215237
theorem B1969099 : Blo 1967435 1969099 := bstep (se 1 (by rfl) ⟨1476824, by rfl⟩ : syracuseStep 1969099 = 2953649) B2953649
theorem B3738221 : Blo 1967435 3738221 := bbase (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) (by norm_num)
theorem B2492147 : Blo 1967435 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B6645725 : Blo 1967435 6645725 := bstep (se 3 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 6645725 = 2492147) B2492147
theorem B4430483 : Blo 1967435 4430483 := bstep (se 1 (by rfl) ⟨3322862, by rfl⟩ : syracuseStep 4430483 = 6645725) B6645725
theorem B2953655 : Blo 1967435 2953655 := bstep (se 1 (by rfl) ⟨2215241, by rfl⟩ : syracuseStep 2953655 = 4430483) B4430483
theorem B1969103 : Blo 1967435 1969103 := bstep (se 1 (by rfl) ⟨1476827, by rfl⟩ : syracuseStep 1969103 = 2953655) B2953655
theorem B2953661 : Blo 1967435 2953661 := bbase (se 3 (by rfl) ⟨553811, by rfl⟩ : syracuseStep 2953661 = 1107623) (by norm_num)
theorem B1969107 : Blo 1967435 1969107 := bstep (se 1 (by rfl) ⟨1476830, by rfl⟩ : syracuseStep 1969107 = 2953661) B2953661
theorem B4430501 : Blo 1967435 4430501 := bbase (se 4 (by rfl) ⟨415359, by rfl⟩ : syracuseStep 4430501 = 830719) (by norm_num)
theorem B2953667 : Blo 1967435 2953667 := bstep (se 1 (by rfl) ⟨2215250, by rfl⟩ : syracuseStep 2953667 = 4430501) B4430501
theorem B1969111 : Blo 1967435 1969111 := bstep (se 1 (by rfl) ⟨1476833, by rfl⟩ : syracuseStep 1969111 = 2953667) B2953667
theorem B4984325 : Blo 1967435 4984325 := bbase (se 4 (by rfl) ⟨467280, by rfl⟩ : syracuseStep 4984325 = 934561) (by norm_num)
theorem B3322883 : Blo 1967435 3322883 := bstep (se 1 (by rfl) ⟨2492162, by rfl⟩ : syracuseStep 3322883 = 4984325) B4984325
theorem B2215255 : Blo 1967435 2215255 := bstep (se 1 (by rfl) ⟨1661441, by rfl⟩ : syracuseStep 2215255 = 3322883) B3322883
theorem B2953673 : Blo 1967435 2953673 := bstep (se 2 (by rfl) ⟨1107627, by rfl⟩ : syracuseStep 2953673 = 2215255) B2215255
theorem B1969115 : Blo 1967435 1969115 := bstep (se 1 (by rfl) ⟨1476836, by rfl⟩ : syracuseStep 1969115 = 2953673) B2953673
theorem B4205533 : Blo 1967435 4205533 := bbase (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) (by norm_num)
theorem B5607377 : Blo 1967435 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B3738251 : Blo 1967435 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B9968669 : Blo 1967435 9968669 := bstep (se 3 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 9968669 = 3738251) B3738251
theorem B6645779 : Blo 1967435 6645779 := bstep (se 1 (by rfl) ⟨4984334, by rfl⟩ : syracuseStep 6645779 = 9968669) B9968669
theorem B4430519 : Blo 1967435 4430519 := bstep (se 1 (by rfl) ⟨3322889, by rfl⟩ : syracuseStep 4430519 = 6645779) B6645779
theorem B2953679 : Blo 1967435 2953679 := bstep (se 1 (by rfl) ⟨2215259, by rfl⟩ : syracuseStep 2953679 = 4430519) B4430519
theorem B1969119 : Blo 1967435 1969119 := bstep (se 1 (by rfl) ⟨1476839, by rfl⟩ : syracuseStep 1969119 = 2953679) B2953679
theorem B2953685 : Blo 1967435 2953685 := bbase (se 7 (by rfl) ⟨34613, by rfl⟩ : syracuseStep 2953685 = 69227) (by norm_num)
theorem B1969123 : Blo 1967435 1969123 := bstep (se 1 (by rfl) ⟨1476842, by rfl⟩ : syracuseStep 1969123 = 2953685) B2953685
theorem B7476533 : Blo 1967435 7476533 := bbase (se 5 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 7476533 = 700925) (by norm_num)
theorem B4984355 : Blo 1967435 4984355 := bstep (se 1 (by rfl) ⟨3738266, by rfl⟩ : syracuseStep 4984355 = 7476533) B7476533
theorem B3322903 : Blo 1967435 3322903 := bstep (se 1 (by rfl) ⟨2492177, by rfl⟩ : syracuseStep 3322903 = 4984355) B4984355
theorem B4430537 : Blo 1967435 4430537 := bstep (se 2 (by rfl) ⟨1661451, by rfl⟩ : syracuseStep 4430537 = 3322903) B3322903
theorem B2953691 : Blo 1967435 2953691 := bstep (se 1 (by rfl) ⟨2215268, by rfl⟩ : syracuseStep 2953691 = 4430537) B4430537
theorem B1969127 : Blo 1967435 1969127 := bstep (se 1 (by rfl) ⟨1476845, by rfl⟩ : syracuseStep 1969127 = 2953691) B2953691
theorem B2215273 : Blo 1967435 2215273 := bbase (se 2 (by rfl) ⟨830727, by rfl⟩ : syracuseStep 2215273 = 1661455) (by norm_num)
theorem B2953697 : Blo 1967435 2953697 := bstep (se 2 (by rfl) ⟨1107636, by rfl⟩ : syracuseStep 2953697 = 2215273) B2215273
theorem B1969131 : Blo 1967435 1969131 := bstep (se 1 (by rfl) ⟨1476848, by rfl⟩ : syracuseStep 1969131 = 2953697) B2953697
theorem B3460789 : Blo 1967435 3460789 := bbase (se 5 (by rfl) ⟨162224, by rfl⟩ : syracuseStep 3460789 = 324449) (by norm_num)
theorem B18457541 : Blo 1967435 18457541 := bstep (se 4 (by rfl) ⟨1730394, by rfl⟩ : syracuseStep 18457541 = 3460789) B3460789
theorem B12305027 : Blo 1967435 12305027 := bstep (se 1 (by rfl) ⟨9228770, by rfl⟩ : syracuseStep 12305027 = 18457541) B18457541
theorem B8203351 : Blo 1967435 8203351 := bstep (se 1 (by rfl) ⟨6152513, by rfl⟩ : syracuseStep 8203351 = 12305027) B12305027
theorem B10937801 : Blo 1967435 10937801 := bstep (se 2 (by rfl) ⟨4101675, by rfl⟩ : syracuseStep 10937801 = 8203351) B8203351
theorem B29167469 : Blo 1967435 29167469 := bstep (se 3 (by rfl) ⟨5468900, by rfl⟩ : syracuseStep 29167469 = 10937801) B10937801
theorem B19444979 : Blo 1967435 19444979 := bstep (se 1 (by rfl) ⟨14583734, by rfl⟩ : syracuseStep 19444979 = 29167469) B29167469
theorem B51853277 : Blo 1967435 51853277 := bstep (se 3 (by rfl) ⟨9722489, by rfl⟩ : syracuseStep 51853277 = 19444979) B19444979
theorem B34568851 : Blo 1967435 34568851 := bstep (se 1 (by rfl) ⟨25926638, by rfl⟩ : syracuseStep 34568851 = 51853277) B51853277
theorem B46091801 : Blo 1967435 46091801 := bstep (se 2 (by rfl) ⟨17284425, by rfl⟩ : syracuseStep 46091801 = 34568851) B34568851
theorem B122911469 : Blo 1967435 122911469 := bstep (se 3 (by rfl) ⟨23045900, by rfl⟩ : syracuseStep 122911469 = 46091801) B46091801
theorem B81940979 : Blo 1967435 81940979 := bstep (se 1 (by rfl) ⟨61455734, by rfl⟩ : syracuseStep 81940979 = 122911469) B122911469
theorem B54627319 : Blo 1967435 54627319 := bstep (se 1 (by rfl) ⟨40970489, by rfl⟩ : syracuseStep 54627319 = 81940979) B81940979
theorem B72836425 : Blo 1967435 72836425 := bstep (se 2 (by rfl) ⟨27313659, by rfl⟩ : syracuseStep 72836425 = 54627319) B54627319
theorem B388460933 : Blo 1967435 388460933 := bstep (se 4 (by rfl) ⟨36418212, by rfl⟩ : syracuseStep 388460933 = 72836425) B72836425
theorem B258973955 : Blo 1967435 258973955 := bstep (se 1 (by rfl) ⟨194230466, by rfl⟩ : syracuseStep 258973955 = 388460933) B388460933
theorem B172649303 : Blo 1967435 172649303 := bstep (se 1 (by rfl) ⟨129486977, by rfl⟩ : syracuseStep 172649303 = 258973955) B258973955
theorem B115099535 : Blo 1967435 115099535 := bstep (se 1 (by rfl) ⟨86324651, by rfl⟩ : syracuseStep 115099535 = 172649303) B172649303
theorem B76733023 : Blo 1967435 76733023 := bstep (se 1 (by rfl) ⟨57549767, by rfl⟩ : syracuseStep 76733023 = 115099535) B115099535
theorem B102310697 : Blo 1967435 102310697 := bstep (se 2 (by rfl) ⟨38366511, by rfl⟩ : syracuseStep 102310697 = 76733023) B76733023
theorem B68207131 : Blo 1967435 68207131 := bstep (se 1 (by rfl) ⟨51155348, by rfl⟩ : syracuseStep 68207131 = 102310697) B102310697
theorem B90942841 : Blo 1967435 90942841 := bstep (se 2 (by rfl) ⟨34103565, by rfl⟩ : syracuseStep 90942841 = 68207131) B68207131
theorem B121257121 : Blo 1967435 121257121 := bstep (se 2 (by rfl) ⟨45471420, by rfl⟩ : syracuseStep 121257121 = 90942841) B90942841
theorem B161676161 : Blo 1967435 161676161 := bstep (se 2 (by rfl) ⟨60628560, by rfl⟩ : syracuseStep 161676161 = 121257121) B121257121
theorem B107784107 : Blo 1967435 107784107 := bstep (se 1 (by rfl) ⟨80838080, by rfl⟩ : syracuseStep 107784107 = 161676161) B161676161
theorem B71856071 : Blo 1967435 71856071 := bstep (se 1 (by rfl) ⟨53892053, by rfl⟩ : syracuseStep 71856071 = 107784107) B107784107
theorem B47904047 : Blo 1967435 47904047 := bstep (se 1 (by rfl) ⟨35928035, by rfl⟩ : syracuseStep 47904047 = 71856071) B71856071
theorem B31936031 : Blo 1967435 31936031 := bstep (se 1 (by rfl) ⟨23952023, by rfl⟩ : syracuseStep 31936031 = 47904047) B47904047
theorem B21290687 : Blo 1967435 21290687 := bstep (se 1 (by rfl) ⟨15968015, by rfl⟩ : syracuseStep 21290687 = 31936031) B31936031
theorem B14193791 : Blo 1967435 14193791 := bstep (se 1 (by rfl) ⟨10645343, by rfl⟩ : syracuseStep 14193791 = 21290687) B21290687
theorem B9462527 : Blo 1967435 9462527 := bstep (se 1 (by rfl) ⟨7096895, by rfl⟩ : syracuseStep 9462527 = 14193791) B14193791
theorem B6308351 : Blo 1967435 6308351 := bstep (se 1 (by rfl) ⟨4731263, by rfl⟩ : syracuseStep 6308351 = 9462527) B9462527
theorem B4205567 : Blo 1967435 4205567 := bstep (se 1 (by rfl) ⟨3154175, by rfl⟩ : syracuseStep 4205567 = 6308351) B6308351
theorem B11214845 : Blo 1967435 11214845 := bstep (se 3 (by rfl) ⟨2102783, by rfl⟩ : syracuseStep 11214845 = 4205567) B4205567
theorem B7476563 : Blo 1967435 7476563 := bstep (se 1 (by rfl) ⟨5607422, by rfl⟩ : syracuseStep 7476563 = 11214845) B11214845
theorem B4984375 : Blo 1967435 4984375 := bstep (se 1 (by rfl) ⟨3738281, by rfl⟩ : syracuseStep 4984375 = 7476563) B7476563
theorem B6645833 : Blo 1967435 6645833 := bstep (se 2 (by rfl) ⟨2492187, by rfl⟩ : syracuseStep 6645833 = 4984375) B4984375
theorem B4430555 : Blo 1967435 4430555 := bstep (se 1 (by rfl) ⟨3322916, by rfl⟩ : syracuseStep 4430555 = 6645833) B6645833
theorem B2953703 : Blo 1967435 2953703 := bstep (se 1 (by rfl) ⟨2215277, by rfl⟩ : syracuseStep 2953703 = 4430555) B4430555
theorem B1969135 : Blo 1967435 1969135 := bstep (se 1 (by rfl) ⟨1476851, by rfl⟩ : syracuseStep 1969135 = 2953703) B2953703
theorem B2953709 : Blo 1967435 2953709 := bbase (se 3 (by rfl) ⟨553820, by rfl⟩ : syracuseStep 2953709 = 1107641) (by norm_num)
theorem B1969139 : Blo 1967435 1969139 := bstep (se 1 (by rfl) ⟨1476854, by rfl⟩ : syracuseStep 1969139 = 2953709) B2953709
theorem B4430573 : Blo 1967435 4430573 := bbase (se 3 (by rfl) ⟨830732, by rfl⟩ : syracuseStep 4430573 = 1661465) (by norm_num)
theorem B2953715 : Blo 1967435 2953715 := bstep (se 1 (by rfl) ⟨2215286, by rfl⟩ : syracuseStep 2953715 = 4430573) B4430573
theorem B1969143 : Blo 1967435 1969143 := bstep (se 1 (by rfl) ⟨1476857, by rfl⟩ : syracuseStep 1969143 = 2953715) B2953715
theorem B2102797 : Blo 1967435 2102797 := bbase (se 3 (by rfl) ⟨394274, by rfl⟩ : syracuseStep 2102797 = 788549) (by norm_num)
theorem B2803729 : Blo 1967435 2803729 := bstep (se 2 (by rfl) ⟨1051398, by rfl⟩ : syracuseStep 2803729 = 2102797) B2102797
theorem B3738305 : Blo 1967435 3738305 := bstep (se 2 (by rfl) ⟨1401864, by rfl⟩ : syracuseStep 3738305 = 2803729) B2803729
theorem B2492203 : Blo 1967435 2492203 := bstep (se 1 (by rfl) ⟨1869152, by rfl⟩ : syracuseStep 2492203 = 3738305) B3738305
theorem B3322937 : Blo 1967435 3322937 := bstep (se 2 (by rfl) ⟨1246101, by rfl⟩ : syracuseStep 3322937 = 2492203) B2492203
theorem B2215291 : Blo 1967435 2215291 := bstep (se 1 (by rfl) ⟨1661468, by rfl⟩ : syracuseStep 2215291 = 3322937) B3322937
theorem B2953721 : Blo 1967435 2953721 := bstep (se 2 (by rfl) ⟨1107645, by rfl⟩ : syracuseStep 2953721 = 2215291) B2215291
theorem B1969147 : Blo 1967435 1969147 := bstep (se 1 (by rfl) ⟨1476860, by rfl⟩ : syracuseStep 1969147 = 2953721) B2953721
theorem B8428789 : Blo 1967435 8428789 := bbase (se 5 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 8428789 = 790199) (by norm_num)
theorem B11238385 : Blo 1967435 11238385 := bstep (se 2 (by rfl) ⟨4214394, by rfl⟩ : syracuseStep 11238385 = 8428789) B8428789
theorem B14984513 : Blo 1967435 14984513 := bstep (se 2 (by rfl) ⟨5619192, by rfl⟩ : syracuseStep 14984513 = 11238385) B11238385
theorem B9989675 : Blo 1967435 9989675 := bstep (se 1 (by rfl) ⟨7492256, by rfl⟩ : syracuseStep 9989675 = 14984513) B14984513
theorem B6659783 : Blo 1967435 6659783 := bstep (se 1 (by rfl) ⟨4994837, by rfl⟩ : syracuseStep 6659783 = 9989675) B9989675
theorem B4439855 : Blo 1967435 4439855 := bstep (se 1 (by rfl) ⟨3329891, by rfl⟩ : syracuseStep 4439855 = 6659783) B6659783
theorem B11839613 : Blo 1967435 11839613 := bstep (se 3 (by rfl) ⟨2219927, by rfl⟩ : syracuseStep 11839613 = 4439855) B4439855
theorem B126289205 : Blo 1967435 126289205 := bstep (se 5 (by rfl) ⟨5919806, by rfl⟩ : syracuseStep 126289205 = 11839613) B11839613
theorem B84192803 : Blo 1967435 84192803 := bstep (se 1 (by rfl) ⟨63144602, by rfl⟩ : syracuseStep 84192803 = 126289205) B126289205
theorem B56128535 : Blo 1967435 56128535 := bstep (se 1 (by rfl) ⟨42096401, by rfl⟩ : syracuseStep 56128535 = 84192803) B84192803
theorem B37419023 : Blo 1967435 37419023 := bstep (se 1 (by rfl) ⟨28064267, by rfl⟩ : syracuseStep 37419023 = 56128535) B56128535
theorem B24946015 : Blo 1967435 24946015 := bstep (se 1 (by rfl) ⟨18709511, by rfl⟩ : syracuseStep 24946015 = 37419023) B37419023
theorem B33261353 : Blo 1967435 33261353 := bstep (se 2 (by rfl) ⟨12473007, by rfl⟩ : syracuseStep 33261353 = 24946015) B24946015
theorem B22174235 : Blo 1967435 22174235 := bstep (se 1 (by rfl) ⟨16630676, by rfl⟩ : syracuseStep 22174235 = 33261353) B33261353
theorem B14782823 : Blo 1967435 14782823 := bstep (se 1 (by rfl) ⟨11087117, by rfl⟩ : syracuseStep 14782823 = 22174235) B22174235
theorem B9855215 : Blo 1967435 9855215 := bstep (se 1 (by rfl) ⟨7391411, by rfl⟩ : syracuseStep 9855215 = 14782823) B14782823
theorem B6570143 : Blo 1967435 6570143 := bstep (se 1 (by rfl) ⟨4927607, by rfl⟩ : syracuseStep 6570143 = 9855215) B9855215
theorem B4380095 : Blo 1967435 4380095 := bstep (se 1 (by rfl) ⟨3285071, by rfl⟩ : syracuseStep 4380095 = 6570143) B6570143
theorem B11680253 : Blo 1967435 11680253 := bstep (se 3 (by rfl) ⟨2190047, by rfl⟩ : syracuseStep 11680253 = 4380095) B4380095
theorem B498357461 : Blo 1967435 498357461 := bstep (se 7 (by rfl) ⟨5840126, by rfl⟩ : syracuseStep 498357461 = 11680253) B11680253
theorem B332238307 : Blo 1967435 332238307 := bstep (se 1 (by rfl) ⟨249178730, by rfl⟩ : syracuseStep 332238307 = 498357461) B498357461
theorem B442984409 : Blo 1967435 442984409 := bstep (se 2 (by rfl) ⟨166119153, by rfl⟩ : syracuseStep 442984409 = 332238307) B332238307
theorem B295322939 : Blo 1967435 295322939 := bstep (se 1 (by rfl) ⟨221492204, by rfl⟩ : syracuseStep 295322939 = 442984409) B442984409
theorem B196881959 : Blo 1967435 196881959 := bstep (se 1 (by rfl) ⟨147661469, by rfl⟩ : syracuseStep 196881959 = 295322939) B295322939
theorem B525018557 : Blo 1967435 525018557 := bstep (se 3 (by rfl) ⟨98440979, by rfl⟩ : syracuseStep 525018557 = 196881959) B196881959
theorem B1400049485 : Blo 1967435 1400049485 := bstep (se 3 (by rfl) ⟨262509278, by rfl⟩ : syracuseStep 1400049485 = 525018557) B525018557
theorem B933366323 : Blo 1967435 933366323 := bstep (se 1 (by rfl) ⟨700024742, by rfl⟩ : syracuseStep 933366323 = 1400049485) B1400049485
theorem B622244215 : Blo 1967435 622244215 := bstep (se 1 (by rfl) ⟨466683161, by rfl⟩ : syracuseStep 622244215 = 933366323) B933366323
theorem B829658953 : Blo 1967435 829658953 := bstep (se 2 (by rfl) ⟨311122107, by rfl⟩ : syracuseStep 829658953 = 622244215) B622244215
theorem B1106211937 : Blo 1967435 1106211937 := bstep (se 2 (by rfl) ⟨414829476, by rfl⟩ : syracuseStep 1106211937 = 829658953) B829658953
theorem B1474949249 : Blo 1967435 1474949249 := bstep (se 2 (by rfl) ⟨553105968, by rfl⟩ : syracuseStep 1474949249 = 1106211937) B1106211937
theorem B983299499 : Blo 1967435 983299499 := bstep (se 1 (by rfl) ⟨737474624, by rfl⟩ : syracuseStep 983299499 = 1474949249) B1474949249
theorem B655532999 : Blo 1967435 655532999 := bstep (se 1 (by rfl) ⟨491649749, by rfl⟩ : syracuseStep 655532999 = 983299499) B983299499
theorem B437021999 : Blo 1967435 437021999 := bstep (se 1 (by rfl) ⟨327766499, by rfl⟩ : syracuseStep 437021999 = 655532999) B655532999
theorem B291347999 : Blo 1967435 291347999 := bstep (se 1 (by rfl) ⟨218510999, by rfl⟩ : syracuseStep 291347999 = 437021999) B437021999
theorem B194231999 : Blo 1967435 194231999 := bstep (se 1 (by rfl) ⟨145673999, by rfl⟩ : syracuseStep 194231999 = 291347999) B291347999
theorem B129487999 : Blo 1967435 129487999 := bstep (se 1 (by rfl) ⟨97115999, by rfl⟩ : syracuseStep 129487999 = 194231999) B194231999
theorem B172650665 : Blo 1967435 172650665 := bstep (se 2 (by rfl) ⟨64743999, by rfl⟩ : syracuseStep 172650665 = 129487999) B129487999
theorem B115100443 : Blo 1967435 115100443 := bstep (se 1 (by rfl) ⟨86325332, by rfl⟩ : syracuseStep 115100443 = 172650665) B172650665
theorem B613869029 : Blo 1967435 613869029 := bstep (se 4 (by rfl) ⟨57550221, by rfl⟩ : syracuseStep 613869029 = 115100443) B115100443
theorem B409246019 : Blo 1967435 409246019 := bstep (se 1 (by rfl) ⟨306934514, by rfl⟩ : syracuseStep 409246019 = 613869029) B613869029
theorem B272830679 : Blo 1967435 272830679 := bstep (se 1 (by rfl) ⟨204623009, by rfl⟩ : syracuseStep 272830679 = 409246019) B409246019
theorem B181887119 : Blo 1967435 181887119 := bstep (se 1 (by rfl) ⟨136415339, by rfl⟩ : syracuseStep 181887119 = 272830679) B272830679
theorem B121258079 : Blo 1967435 121258079 := bstep (se 1 (by rfl) ⟨90943559, by rfl⟩ : syracuseStep 121258079 = 181887119) B181887119
theorem B80838719 : Blo 1967435 80838719 := bstep (se 1 (by rfl) ⟨60629039, by rfl⟩ : syracuseStep 80838719 = 121258079) B121258079
theorem B53892479 : Blo 1967435 53892479 := bstep (se 1 (by rfl) ⟨40419359, by rfl⟩ : syracuseStep 53892479 = 80838719) B80838719
theorem B35928319 : Blo 1967435 35928319 := bstep (se 1 (by rfl) ⟨26946239, by rfl⟩ : syracuseStep 35928319 = 53892479) B53892479
theorem B47904425 : Blo 1967435 47904425 := bstep (se 2 (by rfl) ⟨17964159, by rfl⟩ : syracuseStep 47904425 = 35928319) B35928319
theorem B31936283 : Blo 1967435 31936283 := bstep (se 1 (by rfl) ⟨23952212, by rfl⟩ : syracuseStep 31936283 = 47904425) B47904425
theorem B21290855 : Blo 1967435 21290855 := bstep (se 1 (by rfl) ⟨15968141, by rfl⟩ : syracuseStep 21290855 = 31936283) B31936283
theorem B56775613 : Blo 1967435 56775613 := bstep (se 3 (by rfl) ⟨10645427, by rfl⟩ : syracuseStep 56775613 = 21290855) B21290855
theorem B75700817 : Blo 1967435 75700817 := bstep (se 2 (by rfl) ⟨28387806, by rfl⟩ : syracuseStep 75700817 = 56775613) B56775613
theorem B50467211 : Blo 1967435 50467211 := bstep (se 1 (by rfl) ⟨37850408, by rfl⟩ : syracuseStep 50467211 = 75700817) B75700817
theorem B33644807 : Blo 1967435 33644807 := bstep (se 1 (by rfl) ⟨25233605, by rfl⟩ : syracuseStep 33644807 = 50467211) B50467211
theorem B22429871 : Blo 1967435 22429871 := bstep (se 1 (by rfl) ⟨16822403, by rfl⟩ : syracuseStep 22429871 = 33644807) B33644807
theorem B14953247 : Blo 1967435 14953247 := bstep (se 1 (by rfl) ⟨11214935, by rfl⟩ : syracuseStep 14953247 = 22429871) B22429871
theorem B9968831 : Blo 1967435 9968831 := bstep (se 1 (by rfl) ⟨7476623, by rfl⟩ : syracuseStep 9968831 = 14953247) B14953247
theorem B6645887 : Blo 1967435 6645887 := bstep (se 1 (by rfl) ⟨4984415, by rfl⟩ : syracuseStep 6645887 = 9968831) B9968831
theorem B4430591 : Blo 1967435 4430591 := bstep (se 1 (by rfl) ⟨3322943, by rfl⟩ : syracuseStep 4430591 = 6645887) B6645887
theorem B2953727 : Blo 1967435 2953727 := bstep (se 1 (by rfl) ⟨2215295, by rfl⟩ : syracuseStep 2953727 = 4430591) B4430591
theorem B1969151 : Blo 1967435 1969151 := bstep (se 1 (by rfl) ⟨1476863, by rfl⟩ : syracuseStep 1969151 = 2953727) B2953727
theorem B2953733 : Blo 1967435 2953733 := bbase (se 4 (by rfl) ⟨276912, by rfl⟩ : syracuseStep 2953733 = 553825) (by norm_num)
theorem B1969155 : Blo 1967435 1969155 := bstep (se 1 (by rfl) ⟨1476866, by rfl⟩ : syracuseStep 1969155 = 2953733) B2953733
theorem B3322957 : Blo 1967435 3322957 := bbase (se 3 (by rfl) ⟨623054, by rfl⟩ : syracuseStep 3322957 = 1246109) (by norm_num)
theorem B4430609 : Blo 1967435 4430609 := bstep (se 2 (by rfl) ⟨1661478, by rfl⟩ : syracuseStep 4430609 = 3322957) B3322957
theorem B2953739 : Blo 1967435 2953739 := bstep (se 1 (by rfl) ⟨2215304, by rfl⟩ : syracuseStep 2953739 = 4430609) B4430609
theorem B1969159 : Blo 1967435 1969159 := bstep (se 1 (by rfl) ⟨1476869, by rfl⟩ : syracuseStep 1969159 = 2953739) B2953739
theorem B2215309 : Blo 1967435 2215309 := bbase (se 3 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 2215309 = 830741) (by norm_num)
theorem B2953745 : Blo 1967435 2953745 := bstep (se 2 (by rfl) ⟨1107654, by rfl⟩ : syracuseStep 2953745 = 2215309) B2215309
theorem B1969163 : Blo 1967435 1969163 := bstep (se 1 (by rfl) ⟨1476872, by rfl⟩ : syracuseStep 1969163 = 2953745) B2953745
theorem B6645941 : Blo 1967435 6645941 := bbase (se 5 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 6645941 = 623057) (by norm_num)
theorem B4430627 : Blo 1967435 4430627 := bstep (se 1 (by rfl) ⟨3322970, by rfl⟩ : syracuseStep 4430627 = 6645941) B6645941
theorem B2953751 : Blo 1967435 2953751 := bstep (se 1 (by rfl) ⟨2215313, by rfl⟩ : syracuseStep 2953751 = 4430627) B4430627
theorem B1969167 : Blo 1967435 1969167 := bstep (se 1 (by rfl) ⟨1476875, by rfl⟩ : syracuseStep 1969167 = 2953751) B2953751
theorem B2953757 : Blo 1967435 2953757 := bbase (se 3 (by rfl) ⟨553829, by rfl⟩ : syracuseStep 2953757 = 1107659) (by norm_num)
theorem B1969171 : Blo 1967435 1969171 := bstep (se 1 (by rfl) ⟨1476878, by rfl⟩ : syracuseStep 1969171 = 2953757) B2953757
theorem B4430645 : Blo 1967435 4430645 := bbase (se 5 (by rfl) ⟨207686, by rfl⟩ : syracuseStep 4430645 = 415373) (by norm_num)
theorem B2953763 : Blo 1967435 2953763 := bstep (se 1 (by rfl) ⟨2215322, by rfl⟩ : syracuseStep 2953763 = 4430645) B4430645
theorem B1969175 : Blo 1967435 1969175 := bstep (se 1 (by rfl) ⟨1476881, by rfl⟩ : syracuseStep 1969175 = 2953763) B2953763
theorem B6394565 : Blo 1967435 6394565 := bbase (se 4 (by rfl) ⟨599490, by rfl⟩ : syracuseStep 6394565 = 1198981) (by norm_num)
theorem B4263043 : Blo 1967435 4263043 := bstep (se 1 (by rfl) ⟨3197282, by rfl⟩ : syracuseStep 4263043 = 6394565) B6394565
theorem B5684057 : Blo 1967435 5684057 := bstep (se 2 (by rfl) ⟨2131521, by rfl⟩ : syracuseStep 5684057 = 4263043) B4263043
theorem B3789371 : Blo 1967435 3789371 := bstep (se 1 (by rfl) ⟨2842028, by rfl⟩ : syracuseStep 3789371 = 5684057) B5684057
theorem B2526247 : Blo 1967435 2526247 := bstep (se 1 (by rfl) ⟨1894685, by rfl⟩ : syracuseStep 2526247 = 3789371) B3789371
theorem B13473317 : Blo 1967435 13473317 := bstep (se 4 (by rfl) ⟨1263123, by rfl⟩ : syracuseStep 13473317 = 2526247) B2526247
theorem B8982211 : Blo 1967435 8982211 := bstep (se 1 (by rfl) ⟨6736658, by rfl⟩ : syracuseStep 8982211 = 13473317) B13473317
theorem B11976281 : Blo 1967435 11976281 := bstep (se 2 (by rfl) ⟨4491105, by rfl⟩ : syracuseStep 11976281 = 8982211) B8982211
theorem B7984187 : Blo 1967435 7984187 := bstep (se 1 (by rfl) ⟨5988140, by rfl⟩ : syracuseStep 7984187 = 11976281) B11976281
theorem B5322791 : Blo 1967435 5322791 := bstep (se 1 (by rfl) ⟨3992093, by rfl⟩ : syracuseStep 5322791 = 7984187) B7984187
theorem B14194109 : Blo 1967435 14194109 := bstep (se 3 (by rfl) ⟨2661395, by rfl⟩ : syracuseStep 14194109 = 5322791) B5322791
theorem B9462739 : Blo 1967435 9462739 := bstep (se 1 (by rfl) ⟨7097054, by rfl⟩ : syracuseStep 9462739 = 14194109) B14194109
theorem B12616985 : Blo 1967435 12616985 := bstep (se 2 (by rfl) ⟨4731369, by rfl⟩ : syracuseStep 12616985 = 9462739) B9462739
theorem B8411323 : Blo 1967435 8411323 := bstep (se 1 (by rfl) ⟨6308492, by rfl⟩ : syracuseStep 8411323 = 12616985) B12616985
theorem B11215097 : Blo 1967435 11215097 := bstep (se 2 (by rfl) ⟨4205661, by rfl⟩ : syracuseStep 11215097 = 8411323) B8411323
theorem B7476731 : Blo 1967435 7476731 := bstep (se 1 (by rfl) ⟨5607548, by rfl⟩ : syracuseStep 7476731 = 11215097) B11215097
theorem B4984487 : Blo 1967435 4984487 := bstep (se 1 (by rfl) ⟨3738365, by rfl⟩ : syracuseStep 4984487 = 7476731) B7476731
theorem B3322991 : Blo 1967435 3322991 := bstep (se 1 (by rfl) ⟨2492243, by rfl⟩ : syracuseStep 3322991 = 4984487) B4984487
theorem B2215327 : Blo 1967435 2215327 := bstep (se 1 (by rfl) ⟨1661495, by rfl⟩ : syracuseStep 2215327 = 3322991) B3322991
theorem B2953769 : Blo 1967435 2953769 := bstep (se 2 (by rfl) ⟨1107663, by rfl⟩ : syracuseStep 2953769 = 2215327) B2215327
theorem B1969179 : Blo 1967435 1969179 := bstep (se 1 (by rfl) ⟨1476884, by rfl⟩ : syracuseStep 1969179 = 2953769) B2953769
theorem B9462757 : Blo 1967435 9462757 := bbase (se 4 (by rfl) ⟨887133, by rfl⟩ : syracuseStep 9462757 = 1774267) (by norm_num)
theorem B12617009 : Blo 1967435 12617009 := bstep (se 2 (by rfl) ⟨4731378, by rfl⟩ : syracuseStep 12617009 = 9462757) B9462757
theorem B8411339 : Blo 1967435 8411339 := bstep (se 1 (by rfl) ⟨6308504, by rfl⟩ : syracuseStep 8411339 = 12617009) B12617009
theorem B5607559 : Blo 1967435 5607559 := bstep (se 1 (by rfl) ⟨4205669, by rfl⟩ : syracuseStep 5607559 = 8411339) B8411339
theorem B7476745 : Blo 1967435 7476745 := bstep (se 2 (by rfl) ⟨2803779, by rfl⟩ : syracuseStep 7476745 = 5607559) B5607559
theorem B9968993 : Blo 1967435 9968993 := bstep (se 2 (by rfl) ⟨3738372, by rfl⟩ : syracuseStep 9968993 = 7476745) B7476745
theorem B6645995 : Blo 1967435 6645995 := bstep (se 1 (by rfl) ⟨4984496, by rfl⟩ : syracuseStep 6645995 = 9968993) B9968993
theorem B4430663 : Blo 1967435 4430663 := bstep (se 1 (by rfl) ⟨3322997, by rfl⟩ : syracuseStep 4430663 = 6645995) B6645995
theorem B2953775 : Blo 1967435 2953775 := bstep (se 1 (by rfl) ⟨2215331, by rfl⟩ : syracuseStep 2953775 = 4430663) B4430663
theorem B1969183 : Blo 1967435 1969183 := bstep (se 1 (by rfl) ⟨1476887, by rfl⟩ : syracuseStep 1969183 = 2953775) B2953775
theorem B2953781 : Blo 1967435 2953781 := bbase (se 5 (by rfl) ⟨138458, by rfl⟩ : syracuseStep 2953781 = 276917) (by norm_num)
theorem B1969187 : Blo 1967435 1969187 := bstep (se 1 (by rfl) ⟨1476890, by rfl⟩ : syracuseStep 1969187 = 2953781) B2953781
theorem B4984517 : Blo 1967435 4984517 := bbase (se 4 (by rfl) ⟨467298, by rfl⟩ : syracuseStep 4984517 = 934597) (by norm_num)
theorem B3323011 : Blo 1967435 3323011 := bstep (se 1 (by rfl) ⟨2492258, by rfl⟩ : syracuseStep 3323011 = 4984517) B4984517
theorem B4430681 : Blo 1967435 4430681 := bstep (se 2 (by rfl) ⟨1661505, by rfl⟩ : syracuseStep 4430681 = 3323011) B3323011
theorem B2953787 : Blo 1967435 2953787 := bstep (se 1 (by rfl) ⟨2215340, by rfl⟩ : syracuseStep 2953787 = 4430681) B4430681
theorem B1969191 : Blo 1967435 1969191 := bstep (se 1 (by rfl) ⟨1476893, by rfl⟩ : syracuseStep 1969191 = 2953787) B2953787
theorem B2215345 : Blo 1967435 2215345 := bbase (se 2 (by rfl) ⟨830754, by rfl⟩ : syracuseStep 2215345 = 1661509) (by norm_num)
theorem B2953793 : Blo 1967435 2953793 := bstep (se 2 (by rfl) ⟨1107672, by rfl⟩ : syracuseStep 2953793 = 2215345) B2215345
theorem B1969195 : Blo 1967435 1969195 := bstep (se 1 (by rfl) ⟨1476896, by rfl⟩ : syracuseStep 1969195 = 2953793) B2953793
theorem B5607605 : Blo 1967435 5607605 := bbase (se 5 (by rfl) ⟨262856, by rfl⟩ : syracuseStep 5607605 = 525713) (by norm_num)
theorem B3738403 : Blo 1967435 3738403 := bstep (se 1 (by rfl) ⟨2803802, by rfl⟩ : syracuseStep 3738403 = 5607605) B5607605
theorem B4984537 : Blo 1967435 4984537 := bstep (se 2 (by rfl) ⟨1869201, by rfl⟩ : syracuseStep 4984537 = 3738403) B3738403
theorem B6646049 : Blo 1967435 6646049 := bstep (se 2 (by rfl) ⟨2492268, by rfl⟩ : syracuseStep 6646049 = 4984537) B4984537
theorem B4430699 : Blo 1967435 4430699 := bstep (se 1 (by rfl) ⟨3323024, by rfl⟩ : syracuseStep 4430699 = 6646049) B6646049
theorem B2953799 : Blo 1967435 2953799 := bstep (se 1 (by rfl) ⟨2215349, by rfl⟩ : syracuseStep 2953799 = 4430699) B4430699
theorem B1969199 : Blo 1967435 1969199 := bstep (se 1 (by rfl) ⟨1476899, by rfl⟩ : syracuseStep 1969199 = 2953799) B2953799
theorem B2953805 : Blo 1967435 2953805 := bbase (se 3 (by rfl) ⟨553838, by rfl⟩ : syracuseStep 2953805 = 1107677) (by norm_num)
theorem B1969203 : Blo 1967435 1969203 := bstep (se 1 (by rfl) ⟨1476902, by rfl⟩ : syracuseStep 1969203 = 2953805) B2953805
theorem B4430717 : Blo 1967435 4430717 := bbase (se 3 (by rfl) ⟨830759, by rfl⟩ : syracuseStep 4430717 = 1661519) (by norm_num)
theorem B2953811 : Blo 1967435 2953811 := bstep (se 1 (by rfl) ⟨2215358, by rfl⟩ : syracuseStep 2953811 = 4430717) B4430717
theorem B1969207 : Blo 1967435 1969207 := bstep (se 1 (by rfl) ⟨1476905, by rfl⟩ : syracuseStep 1969207 = 2953811) B2953811
theorem B3323045 : Blo 1967435 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B2215363 : Blo 1967435 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B2953817 : Blo 1967435 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B1969211 : Blo 1967435 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B2102869 : Blo 1967435 2102869 := bbase (se 8 (by rfl) ⟨12321, by rfl⟩ : syracuseStep 2102869 = 24643) (by norm_num)
theorem B2803825 : Blo 1967435 2803825 := bstep (se 2 (by rfl) ⟨1051434, by rfl⟩ : syracuseStep 2803825 = 2102869) B2102869
theorem B14953733 : Blo 1967435 14953733 := bstep (se 4 (by rfl) ⟨1401912, by rfl⟩ : syracuseStep 14953733 = 2803825) B2803825
theorem B9969155 : Blo 1967435 9969155 := bstep (se 1 (by rfl) ⟨7476866, by rfl⟩ : syracuseStep 9969155 = 14953733) B14953733
theorem B6646103 : Blo 1967435 6646103 := bstep (se 1 (by rfl) ⟨4984577, by rfl⟩ : syracuseStep 6646103 = 9969155) B9969155
theorem B4430735 : Blo 1967435 4430735 := bstep (se 1 (by rfl) ⟨3323051, by rfl⟩ : syracuseStep 4430735 = 6646103) B6646103
theorem B2953823 : Blo 1967435 2953823 := bstep (se 1 (by rfl) ⟨2215367, by rfl⟩ : syracuseStep 2953823 = 4430735) B4430735
theorem B1969215 : Blo 1967435 1969215 := bstep (se 1 (by rfl) ⟨1476911, by rfl⟩ : syracuseStep 1969215 = 2953823) B2953823
theorem B2953829 : Blo 1967435 2953829 := bbase (se 4 (by rfl) ⟨276921, by rfl⟩ : syracuseStep 2953829 = 553843) (by norm_num)
theorem B1969219 : Blo 1967435 1969219 := bstep (se 1 (by rfl) ⟨1476914, by rfl⟩ : syracuseStep 1969219 = 2953829) B2953829
theorem B2803837 : Blo 1967435 2803837 := bbase (se 3 (by rfl) ⟨525719, by rfl⟩ : syracuseStep 2803837 = 1051439) (by norm_num)
theorem B3738449 : Blo 1967435 3738449 := bstep (se 2 (by rfl) ⟨1401918, by rfl⟩ : syracuseStep 3738449 = 2803837) B2803837
theorem B2492299 : Blo 1967435 2492299 := bstep (se 1 (by rfl) ⟨1869224, by rfl⟩ : syracuseStep 2492299 = 3738449) B3738449
theorem B3323065 : Blo 1967435 3323065 := bstep (se 2 (by rfl) ⟨1246149, by rfl⟩ : syracuseStep 3323065 = 2492299) B2492299
theorem B4430753 : Blo 1967435 4430753 := bstep (se 2 (by rfl) ⟨1661532, by rfl⟩ : syracuseStep 4430753 = 3323065) B3323065
theorem B2953835 : Blo 1967435 2953835 := bstep (se 1 (by rfl) ⟨2215376, by rfl⟩ : syracuseStep 2953835 = 4430753) B4430753
theorem B1969223 : Blo 1967435 1969223 := bstep (se 1 (by rfl) ⟨1476917, by rfl⟩ : syracuseStep 1969223 = 2953835) B2953835
theorem B2215381 : Blo 1967435 2215381 := bbase (se 7 (by rfl) ⟨25961, by rfl⟩ : syracuseStep 2215381 = 51923) (by norm_num)
theorem B2953841 : Blo 1967435 2953841 := bstep (se 2 (by rfl) ⟨1107690, by rfl⟩ : syracuseStep 2953841 = 2215381) B2215381
theorem B1969227 : Blo 1967435 1969227 := bstep (se 1 (by rfl) ⟨1476920, by rfl⟩ : syracuseStep 1969227 = 2953841) B2953841
theorem B2492309 : Blo 1967435 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B6646157 : Blo 1967435 6646157 := bstep (se 3 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 6646157 = 2492309) B2492309
theorem B4430771 : Blo 1967435 4430771 := bstep (se 1 (by rfl) ⟨3323078, by rfl⟩ : syracuseStep 4430771 = 6646157) B6646157
theorem B2953847 : Blo 1967435 2953847 := bstep (se 1 (by rfl) ⟨2215385, by rfl⟩ : syracuseStep 2953847 = 4430771) B4430771
theorem B1969231 : Blo 1967435 1969231 := bstep (se 1 (by rfl) ⟨1476923, by rfl⟩ : syracuseStep 1969231 = 2953847) B2953847
theorem B2953853 : Blo 1967435 2953853 := bbase (se 3 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 2953853 = 1107695) (by norm_num)
theorem B1969235 : Blo 1967435 1969235 := bstep (se 1 (by rfl) ⟨1476926, by rfl⟩ : syracuseStep 1969235 = 2953853) B2953853
theorem B4430789 : Blo 1967435 4430789 := bbase (se 4 (by rfl) ⟨415386, by rfl⟩ : syracuseStep 4430789 = 830773) (by norm_num)
theorem B2953859 : Blo 1967435 2953859 := bstep (se 1 (by rfl) ⟨2215394, by rfl⟩ : syracuseStep 2953859 = 4430789) B4430789
theorem B1969239 : Blo 1967435 1969239 := bstep (se 1 (by rfl) ⟨1476929, by rfl⟩ : syracuseStep 1969239 = 2953859) B2953859
theorem B3154349 : Blo 1967435 3154349 := bbase (se 3 (by rfl) ⟨591440, by rfl⟩ : syracuseStep 3154349 = 1182881) (by norm_num)
theorem B8411597 : Blo 1967435 8411597 := bstep (se 3 (by rfl) ⟨1577174, by rfl⟩ : syracuseStep 8411597 = 3154349) B3154349
theorem B5607731 : Blo 1967435 5607731 := bstep (se 1 (by rfl) ⟨4205798, by rfl⟩ : syracuseStep 5607731 = 8411597) B8411597
theorem B3738487 : Blo 1967435 3738487 := bstep (se 1 (by rfl) ⟨2803865, by rfl⟩ : syracuseStep 3738487 = 5607731) B5607731
theorem B4984649 : Blo 1967435 4984649 := bstep (se 2 (by rfl) ⟨1869243, by rfl⟩ : syracuseStep 4984649 = 3738487) B3738487
theorem B3323099 : Blo 1967435 3323099 := bstep (se 1 (by rfl) ⟨2492324, by rfl⟩ : syracuseStep 3323099 = 4984649) B4984649
theorem B2215399 : Blo 1967435 2215399 := bstep (se 1 (by rfl) ⟨1661549, by rfl⟩ : syracuseStep 2215399 = 3323099) B3323099
theorem B2953865 : Blo 1967435 2953865 := bstep (se 2 (by rfl) ⟨1107699, by rfl⟩ : syracuseStep 2953865 = 2215399) B2215399
theorem B1969243 : Blo 1967435 1969243 := bstep (se 1 (by rfl) ⟨1476932, by rfl⟩ : syracuseStep 1969243 = 2953865) B2953865
theorem B9969317 : Blo 1967435 9969317 := bbase (se 4 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 9969317 = 1869247) (by norm_num)
theorem B6646211 : Blo 1967435 6646211 := bstep (se 1 (by rfl) ⟨4984658, by rfl⟩ : syracuseStep 6646211 = 9969317) B9969317
theorem B4430807 : Blo 1967435 4430807 := bstep (se 1 (by rfl) ⟨3323105, by rfl⟩ : syracuseStep 4430807 = 6646211) B6646211
theorem B2953871 : Blo 1967435 2953871 := bstep (se 1 (by rfl) ⟨2215403, by rfl⟩ : syracuseStep 2953871 = 4430807) B4430807
theorem B1969247 : Blo 1967435 1969247 := bstep (se 1 (by rfl) ⟨1476935, by rfl⟩ : syracuseStep 1969247 = 2953871) B2953871
theorem B2953877 : Blo 1967435 2953877 := bbase (se 6 (by rfl) ⟨69231, by rfl⟩ : syracuseStep 2953877 = 138463) (by norm_num)
theorem B1969251 : Blo 1967435 1969251 := bstep (se 1 (by rfl) ⟨1476938, by rfl⟩ : syracuseStep 1969251 = 2953877) B2953877
theorem B4861541 : Blo 1967435 4861541 := bbase (se 4 (by rfl) ⟨455769, by rfl⟩ : syracuseStep 4861541 = 911539) (by norm_num)
theorem B12964109 : Blo 1967435 12964109 := bstep (se 3 (by rfl) ⟨2430770, by rfl⟩ : syracuseStep 12964109 = 4861541) B4861541
theorem B34570957 : Blo 1967435 34570957 := bstep (se 3 (by rfl) ⟨6482054, by rfl⟩ : syracuseStep 34570957 = 12964109) B12964109
theorem B46094609 : Blo 1967435 46094609 := bstep (se 2 (by rfl) ⟨17285478, by rfl⟩ : syracuseStep 46094609 = 34570957) B34570957
theorem B30729739 : Blo 1967435 30729739 := bstep (se 1 (by rfl) ⟨23047304, by rfl⟩ : syracuseStep 30729739 = 46094609) B46094609
theorem B40972985 : Blo 1967435 40972985 := bstep (se 2 (by rfl) ⟨15364869, by rfl⟩ : syracuseStep 40972985 = 30729739) B30729739
theorem B27315323 : Blo 1967435 27315323 := bstep (se 1 (by rfl) ⟨20486492, by rfl⟩ : syracuseStep 27315323 = 40972985) B40972985
theorem B18210215 : Blo 1967435 18210215 := bstep (se 1 (by rfl) ⟨13657661, by rfl⟩ : syracuseStep 18210215 = 27315323) B27315323
theorem B48560573 : Blo 1967435 48560573 := bstep (se 3 (by rfl) ⟨9105107, by rfl⟩ : syracuseStep 48560573 = 18210215) B18210215
theorem B129494861 : Blo 1967435 129494861 := bstep (se 3 (by rfl) ⟨24280286, by rfl⟩ : syracuseStep 129494861 = 48560573) B48560573
theorem B86329907 : Blo 1967435 86329907 := bstep (se 1 (by rfl) ⟨64747430, by rfl⟩ : syracuseStep 86329907 = 129494861) B129494861
theorem B57553271 : Blo 1967435 57553271 := bstep (se 1 (by rfl) ⟨43164953, by rfl⟩ : syracuseStep 57553271 = 86329907) B86329907
theorem B38368847 : Blo 1967435 38368847 := bstep (se 1 (by rfl) ⟨28776635, by rfl⟩ : syracuseStep 38368847 = 57553271) B57553271
theorem B102316925 : Blo 1967435 102316925 := bstep (se 3 (by rfl) ⟨19184423, by rfl⟩ : syracuseStep 102316925 = 38368847) B38368847
theorem B68211283 : Blo 1967435 68211283 := bstep (se 1 (by rfl) ⟨51158462, by rfl⟩ : syracuseStep 68211283 = 102316925) B102316925
theorem B90948377 : Blo 1967435 90948377 := bstep (se 2 (by rfl) ⟨34105641, by rfl⟩ : syracuseStep 90948377 = 68211283) B68211283
theorem B242529005 : Blo 1967435 242529005 := bstep (se 3 (by rfl) ⟨45474188, by rfl⟩ : syracuseStep 242529005 = 90948377) B90948377
theorem B161686003 : Blo 1967435 161686003 := bstep (se 1 (by rfl) ⟨121264502, by rfl⟩ : syracuseStep 161686003 = 242529005) B242529005
theorem B215581337 : Blo 1967435 215581337 := bstep (se 2 (by rfl) ⟨80843001, by rfl⟩ : syracuseStep 215581337 = 161686003) B161686003
theorem B143720891 : Blo 1967435 143720891 := bstep (se 1 (by rfl) ⟨107790668, by rfl⟩ : syracuseStep 143720891 = 215581337) B215581337
theorem B95813927 : Blo 1967435 95813927 := bstep (se 1 (by rfl) ⟨71860445, by rfl⟩ : syracuseStep 95813927 = 143720891) B143720891
theorem B63875951 : Blo 1967435 63875951 := bstep (se 1 (by rfl) ⟨47906963, by rfl⟩ : syracuseStep 63875951 = 95813927) B95813927
theorem B42583967 : Blo 1967435 42583967 := bstep (se 1 (by rfl) ⟨31937975, by rfl⟩ : syracuseStep 42583967 = 63875951) B63875951
theorem B28389311 : Blo 1967435 28389311 := bstep (se 1 (by rfl) ⟨21291983, by rfl⟩ : syracuseStep 28389311 = 42583967) B42583967
theorem B18926207 : Blo 1967435 18926207 := bstep (se 1 (by rfl) ⟨14194655, by rfl⟩ : syracuseStep 18926207 = 28389311) B28389311
theorem B12617471 : Blo 1967435 12617471 := bstep (se 1 (by rfl) ⟨9463103, by rfl⟩ : syracuseStep 12617471 = 18926207) B18926207
theorem B8411647 : Blo 1967435 8411647 := bstep (se 1 (by rfl) ⟨6308735, by rfl⟩ : syracuseStep 8411647 = 12617471) B12617471
theorem B11215529 : Blo 1967435 11215529 := bstep (se 2 (by rfl) ⟨4205823, by rfl⟩ : syracuseStep 11215529 = 8411647) B8411647
theorem B7477019 : Blo 1967435 7477019 := bstep (se 1 (by rfl) ⟨5607764, by rfl⟩ : syracuseStep 7477019 = 11215529) B11215529
theorem B4984679 : Blo 1967435 4984679 := bstep (se 1 (by rfl) ⟨3738509, by rfl⟩ : syracuseStep 4984679 = 7477019) B7477019
theorem B3323119 : Blo 1967435 3323119 := bstep (se 1 (by rfl) ⟨2492339, by rfl⟩ : syracuseStep 3323119 = 4984679) B4984679
theorem B4430825 : Blo 1967435 4430825 := bstep (se 2 (by rfl) ⟨1661559, by rfl⟩ : syracuseStep 4430825 = 3323119) B3323119
theorem B2953883 : Blo 1967435 2953883 := bstep (se 1 (by rfl) ⟨2215412, by rfl⟩ : syracuseStep 2953883 = 4430825) B4430825
theorem B1969255 : Blo 1967435 1969255 := bstep (se 1 (by rfl) ⟨1476941, by rfl⟩ : syracuseStep 1969255 = 2953883) B2953883
theorem B2215417 : Blo 1967435 2215417 := bbase (se 2 (by rfl) ⟨830781, by rfl⟩ : syracuseStep 2215417 = 1661563) (by norm_num)
theorem B2953889 : Blo 1967435 2953889 := bstep (se 2 (by rfl) ⟨1107708, by rfl⟩ : syracuseStep 2953889 = 2215417) B2215417
theorem B1969259 : Blo 1967435 1969259 := bstep (se 1 (by rfl) ⟨1476944, by rfl⟩ : syracuseStep 1969259 = 2953889) B2953889
theorem B2661509 : Blo 1967435 2661509 := bbase (se 4 (by rfl) ⟨249516, by rfl⟩ : syracuseStep 2661509 = 499033) (by norm_num)
theorem B7097357 : Blo 1967435 7097357 := bstep (se 3 (by rfl) ⟨1330754, by rfl⟩ : syracuseStep 7097357 = 2661509) B2661509
theorem B4731571 : Blo 1967435 4731571 := bstep (se 1 (by rfl) ⟨3548678, by rfl⟩ : syracuseStep 4731571 = 7097357) B7097357
theorem B6308761 : Blo 1967435 6308761 := bstep (se 2 (by rfl) ⟨2365785, by rfl⟩ : syracuseStep 6308761 = 4731571) B4731571
theorem B8411681 : Blo 1967435 8411681 := bstep (se 2 (by rfl) ⟨3154380, by rfl⟩ : syracuseStep 8411681 = 6308761) B6308761
theorem B5607787 : Blo 1967435 5607787 := bstep (se 1 (by rfl) ⟨4205840, by rfl⟩ : syracuseStep 5607787 = 8411681) B8411681
theorem B7477049 : Blo 1967435 7477049 := bstep (se 2 (by rfl) ⟨2803893, by rfl⟩ : syracuseStep 7477049 = 5607787) B5607787
theorem B4984699 : Blo 1967435 4984699 := bstep (se 1 (by rfl) ⟨3738524, by rfl⟩ : syracuseStep 4984699 = 7477049) B7477049
theorem B6646265 : Blo 1967435 6646265 := bstep (se 2 (by rfl) ⟨2492349, by rfl⟩ : syracuseStep 6646265 = 4984699) B4984699
theorem B4430843 : Blo 1967435 4430843 := bstep (se 1 (by rfl) ⟨3323132, by rfl⟩ : syracuseStep 4430843 = 6646265) B6646265
theorem B2953895 : Blo 1967435 2953895 := bstep (se 1 (by rfl) ⟨2215421, by rfl⟩ : syracuseStep 2953895 = 4430843) B4430843
theorem B1969263 : Blo 1967435 1969263 := bstep (se 1 (by rfl) ⟨1476947, by rfl⟩ : syracuseStep 1969263 = 2953895) B2953895
theorem B2953901 : Blo 1967435 2953901 := bbase (se 3 (by rfl) ⟨553856, by rfl⟩ : syracuseStep 2953901 = 1107713) (by norm_num)
theorem B1969267 : Blo 1967435 1969267 := bstep (se 1 (by rfl) ⟨1476950, by rfl⟩ : syracuseStep 1969267 = 2953901) B2953901
theorem B4430861 : Blo 1967435 4430861 := bbase (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) (by norm_num)
theorem B2953907 : Blo 1967435 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B1969271 : Blo 1967435 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B2492365 : Blo 1967435 2492365 := bbase (se 3 (by rfl) ⟨467318, by rfl⟩ : syracuseStep 2492365 = 934637) (by norm_num)
theorem B3323153 : Blo 1967435 3323153 := bstep (se 2 (by rfl) ⟨1246182, by rfl⟩ : syracuseStep 3323153 = 2492365) B2492365
theorem B2215435 : Blo 1967435 2215435 := bstep (se 1 (by rfl) ⟨1661576, by rfl⟩ : syracuseStep 2215435 = 3323153) B3323153
theorem B2953913 : Blo 1967435 2953913 := bstep (se 2 (by rfl) ⟨1107717, by rfl⟩ : syracuseStep 2953913 = 2215435) B2215435
theorem B1969275 : Blo 1967435 1969275 := bstep (se 1 (by rfl) ⟨1476956, by rfl⟩ : syracuseStep 1969275 = 2953913) B2953913
theorem B28389653 : Blo 1967435 28389653 := bbase (se 6 (by rfl) ⟨665382, by rfl⟩ : syracuseStep 28389653 = 1330765) (by norm_num)
theorem B18926435 : Blo 1967435 18926435 := bstep (se 1 (by rfl) ⟨14194826, by rfl⟩ : syracuseStep 18926435 = 28389653) B28389653
theorem B12617623 : Blo 1967435 12617623 := bstep (se 1 (by rfl) ⟨9463217, by rfl⟩ : syracuseStep 12617623 = 18926435) B18926435
theorem B16823497 : Blo 1967435 16823497 := bstep (se 2 (by rfl) ⟨6308811, by rfl⟩ : syracuseStep 16823497 = 12617623) B12617623
theorem B22431329 : Blo 1967435 22431329 := bstep (se 2 (by rfl) ⟨8411748, by rfl⟩ : syracuseStep 22431329 = 16823497) B16823497
theorem B14954219 : Blo 1967435 14954219 := bstep (se 1 (by rfl) ⟨11215664, by rfl⟩ : syracuseStep 14954219 = 22431329) B22431329
theorem B9969479 : Blo 1967435 9969479 := bstep (se 1 (by rfl) ⟨7477109, by rfl⟩ : syracuseStep 9969479 = 14954219) B14954219
theorem B6646319 : Blo 1967435 6646319 := bstep (se 1 (by rfl) ⟨4984739, by rfl⟩ : syracuseStep 6646319 = 9969479) B9969479
theorem B4430879 : Blo 1967435 4430879 := bstep (se 1 (by rfl) ⟨3323159, by rfl⟩ : syracuseStep 4430879 = 6646319) B6646319
theorem B2953919 : Blo 1967435 2953919 := bstep (se 1 (by rfl) ⟨2215439, by rfl⟩ : syracuseStep 2953919 = 4430879) B4430879
theorem B1969279 : Blo 1967435 1969279 := bstep (se 1 (by rfl) ⟨1476959, by rfl⟩ : syracuseStep 1969279 = 2953919) B2953919
theorem B2953925 : Blo 1967435 2953925 := bbase (se 4 (by rfl) ⟨276930, by rfl⟩ : syracuseStep 2953925 = 553861) (by norm_num)
theorem B1969283 : Blo 1967435 1969283 := bstep (se 1 (by rfl) ⟨1476962, by rfl⟩ : syracuseStep 1969283 = 2953925) B2953925
theorem B3323173 : Blo 1967435 3323173 := bbase (se 4 (by rfl) ⟨311547, by rfl⟩ : syracuseStep 3323173 = 623095) (by norm_num)
theorem B4430897 : Blo 1967435 4430897 := bstep (se 2 (by rfl) ⟨1661586, by rfl⟩ : syracuseStep 4430897 = 3323173) B3323173
theorem B2953931 : Blo 1967435 2953931 := bstep (se 1 (by rfl) ⟨2215448, by rfl⟩ : syracuseStep 2953931 = 4430897) B4430897
theorem B1969287 : Blo 1967435 1969287 := bstep (se 1 (by rfl) ⟨1476965, by rfl⟩ : syracuseStep 1969287 = 2953931) B2953931
theorem B2215453 : Blo 1967435 2215453 := bbase (se 3 (by rfl) ⟨415397, by rfl⟩ : syracuseStep 2215453 = 830795) (by norm_num)
theorem B2953937 : Blo 1967435 2953937 := bstep (se 2 (by rfl) ⟨1107726, by rfl⟩ : syracuseStep 2953937 = 2215453) B2215453
theorem B1969291 : Blo 1967435 1969291 := bstep (se 1 (by rfl) ⟨1476968, by rfl⟩ : syracuseStep 1969291 = 2953937) B2953937
theorem B6646373 : Blo 1967435 6646373 := bbase (se 4 (by rfl) ⟨623097, by rfl⟩ : syracuseStep 6646373 = 1246195) (by norm_num)
theorem B4430915 : Blo 1967435 4430915 := bstep (se 1 (by rfl) ⟨3323186, by rfl⟩ : syracuseStep 4430915 = 6646373) B6646373
theorem B2953943 : Blo 1967435 2953943 := bstep (se 1 (by rfl) ⟨2215457, by rfl⟩ : syracuseStep 2953943 = 4430915) B4430915
theorem B1969295 : Blo 1967435 1969295 := bstep (se 1 (by rfl) ⟨1476971, by rfl⟩ : syracuseStep 1969295 = 2953943) B2953943
theorem B2953949 : Blo 1967435 2953949 := bbase (se 3 (by rfl) ⟨553865, by rfl⟩ : syracuseStep 2953949 = 1107731) (by norm_num)
theorem B1969299 : Blo 1967435 1969299 := bstep (se 1 (by rfl) ⟨1476974, by rfl⟩ : syracuseStep 1969299 = 2953949) B2953949
theorem B4430933 : Blo 1967435 4430933 := bbase (se 8 (by rfl) ⟨25962, by rfl⟩ : syracuseStep 4430933 = 51925) (by norm_num)
theorem B2953955 : Blo 1967435 2953955 := bstep (se 1 (by rfl) ⟨2215466, by rfl⟩ : syracuseStep 2953955 = 4430933) B4430933
theorem B1969303 : Blo 1967435 1969303 := bstep (se 1 (by rfl) ⟨1476977, by rfl⟩ : syracuseStep 1969303 = 2953955) B2953955
theorem B3368549 : Blo 1967435 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B2245699 : Blo 1967435 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2994265 : Blo 1967435 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B15969413 : Blo 1967435 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B10646275 : Blo 1967435 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B14195033 : Blo 1967435 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B9463355 : Blo 1967435 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B6308903 : Blo 1967435 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B4205935 : Blo 1967435 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B5607913 : Blo 1967435 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B7477217 : Blo 1967435 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B4984811 : Blo 1967435 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B3323207 : Blo 1967435 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B2215471 : Blo 1967435 2215471 := bstep (se 1 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 2215471 = 3323207) B3323207
theorem B2953961 : Blo 1967435 2953961 := bstep (se 2 (by rfl) ⟨1107735, by rfl⟩ : syracuseStep 2953961 = 2215471) B2215471
theorem B1969307 : Blo 1967435 1969307 := bstep (se 1 (by rfl) ⟨1476980, by rfl⟩ : syracuseStep 1969307 = 2953961) B2953961
theorem B42585173 : Blo 1967435 42585173 := bbase (se 8 (by rfl) ⟨249522, by rfl⟩ : syracuseStep 42585173 = 499045) (by norm_num)
theorem B28390115 : Blo 1967435 28390115 := bstep (se 1 (by rfl) ⟨21292586, by rfl⟩ : syracuseStep 28390115 = 42585173) B42585173
theorem B18926743 : Blo 1967435 18926743 := bstep (se 1 (by rfl) ⟨14195057, by rfl⟩ : syracuseStep 18926743 = 28390115) B28390115
theorem B25235657 : Blo 1967435 25235657 := bstep (se 2 (by rfl) ⟨9463371, by rfl⟩ : syracuseStep 25235657 = 18926743) B18926743
theorem B16823771 : Blo 1967435 16823771 := bstep (se 1 (by rfl) ⟨12617828, by rfl⟩ : syracuseStep 16823771 = 25235657) B25235657
theorem B11215847 : Blo 1967435 11215847 := bstep (se 1 (by rfl) ⟨8411885, by rfl⟩ : syracuseStep 11215847 = 16823771) B16823771
theorem B7477231 : Blo 1967435 7477231 := bstep (se 1 (by rfl) ⟨5607923, by rfl⟩ : syracuseStep 7477231 = 11215847) B11215847
theorem B9969641 : Blo 1967435 9969641 := bstep (se 2 (by rfl) ⟨3738615, by rfl⟩ : syracuseStep 9969641 = 7477231) B7477231
theorem B6646427 : Blo 1967435 6646427 := bstep (se 1 (by rfl) ⟨4984820, by rfl⟩ : syracuseStep 6646427 = 9969641) B9969641
theorem B4430951 : Blo 1967435 4430951 := bstep (se 1 (by rfl) ⟨3323213, by rfl⟩ : syracuseStep 4430951 = 6646427) B6646427
theorem B2953967 : Blo 1967435 2953967 := bstep (se 1 (by rfl) ⟨2215475, by rfl⟩ : syracuseStep 2953967 = 4430951) B4430951
theorem B1969311 : Blo 1967435 1969311 := bstep (se 1 (by rfl) ⟨1476983, by rfl⟩ : syracuseStep 1969311 = 2953967) B2953967
theorem B2953973 : Blo 1967435 2953973 := bbase (se 5 (by rfl) ⟨138467, by rfl⟩ : syracuseStep 2953973 = 276935) (by norm_num)
theorem B1969315 : Blo 1967435 1969315 := bstep (se 1 (by rfl) ⟨1476986, by rfl⟩ : syracuseStep 1969315 = 2953973) B2953973
theorem B2365853 : Blo 1967435 2365853 := bbase (se 3 (by rfl) ⟨443597, by rfl⟩ : syracuseStep 2365853 = 887195) (by norm_num)
theorem B6308941 : Blo 1967435 6308941 := bstep (se 3 (by rfl) ⟨1182926, by rfl⟩ : syracuseStep 6308941 = 2365853) B2365853
theorem B8411921 : Blo 1967435 8411921 := bstep (se 2 (by rfl) ⟨3154470, by rfl⟩ : syracuseStep 8411921 = 6308941) B6308941
theorem B5607947 : Blo 1967435 5607947 := bstep (se 1 (by rfl) ⟨4205960, by rfl⟩ : syracuseStep 5607947 = 8411921) B8411921
theorem B3738631 : Blo 1967435 3738631 := bstep (se 1 (by rfl) ⟨2803973, by rfl⟩ : syracuseStep 3738631 = 5607947) B5607947
theorem B4984841 : Blo 1967435 4984841 := bstep (se 2 (by rfl) ⟨1869315, by rfl⟩ : syracuseStep 4984841 = 3738631) B3738631
theorem B3323227 : Blo 1967435 3323227 := bstep (se 1 (by rfl) ⟨2492420, by rfl⟩ : syracuseStep 3323227 = 4984841) B4984841
theorem B4430969 : Blo 1967435 4430969 := bstep (se 2 (by rfl) ⟨1661613, by rfl⟩ : syracuseStep 4430969 = 3323227) B3323227
theorem B2953979 : Blo 1967435 2953979 := bstep (se 1 (by rfl) ⟨2215484, by rfl⟩ : syracuseStep 2953979 = 4430969) B4430969
theorem B1969319 : Blo 1967435 1969319 := bstep (se 1 (by rfl) ⟨1476989, by rfl⟩ : syracuseStep 1969319 = 2953979) B2953979
theorem B2215489 : Blo 1967435 2215489 := bbase (se 2 (by rfl) ⟨830808, by rfl⟩ : syracuseStep 2215489 = 1661617) (by norm_num)
theorem B2953985 : Blo 1967435 2953985 := bstep (se 2 (by rfl) ⟨1107744, by rfl⟩ : syracuseStep 2953985 = 2215489) B2215489
theorem B1969323 : Blo 1967435 1969323 := bstep (se 1 (by rfl) ⟨1476992, by rfl⟩ : syracuseStep 1969323 = 2953985) B2953985
theorem B4984861 : Blo 1967435 4984861 := bbase (se 3 (by rfl) ⟨934661, by rfl⟩ : syracuseStep 4984861 = 1869323) (by norm_num)
theorem B6646481 : Blo 1967435 6646481 := bstep (se 2 (by rfl) ⟨2492430, by rfl⟩ : syracuseStep 6646481 = 4984861) B4984861
theorem B4430987 : Blo 1967435 4430987 := bstep (se 1 (by rfl) ⟨3323240, by rfl⟩ : syracuseStep 4430987 = 6646481) B6646481
theorem B2953991 : Blo 1967435 2953991 := bstep (se 1 (by rfl) ⟨2215493, by rfl⟩ : syracuseStep 2953991 = 4430987) B4430987
theorem B1969327 : Blo 1967435 1969327 := bstep (se 1 (by rfl) ⟨1476995, by rfl⟩ : syracuseStep 1969327 = 2953991) B2953991
theorem B2953997 : Blo 1967435 2953997 := bbase (se 3 (by rfl) ⟨553874, by rfl⟩ : syracuseStep 2953997 = 1107749) (by norm_num)
theorem B1969331 : Blo 1967435 1969331 := bstep (se 1 (by rfl) ⟨1476998, by rfl⟩ : syracuseStep 1969331 = 2953997) B2953997
theorem B4431005 : Blo 1967435 4431005 := bbase (se 3 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 4431005 = 1661627) (by norm_num)
theorem B2954003 : Blo 1967435 2954003 := bstep (se 1 (by rfl) ⟨2215502, by rfl⟩ : syracuseStep 2954003 = 4431005) B4431005
theorem B1969335 : Blo 1967435 1969335 := bstep (se 1 (by rfl) ⟨1477001, by rfl⟩ : syracuseStep 1969335 = 2954003) B2954003
theorem B3323261 : Blo 1967435 3323261 := bbase (se 3 (by rfl) ⟨623111, by rfl⟩ : syracuseStep 3323261 = 1246223) (by norm_num)
theorem B2215507 : Blo 1967435 2215507 := bstep (se 1 (by rfl) ⟨1661630, by rfl⟩ : syracuseStep 2215507 = 3323261) B3323261
theorem B2954009 : Blo 1967435 2954009 := bstep (se 2 (by rfl) ⟨1107753, by rfl⟩ : syracuseStep 2954009 = 2215507) B2215507
theorem B1969339 : Blo 1967435 1969339 := bstep (se 1 (by rfl) ⟨1477004, by rfl⟩ : syracuseStep 1969339 = 2954009) B2954009
theorem B1996213 : Blo 1967435 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B2661617 : Blo 1967435 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B7097645 : Blo 1967435 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B4731763 : Blo 1967435 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B6309017 : Blo 1967435 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B4206011 : Blo 1967435 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B11216029 : Blo 1967435 11216029 := bstep (se 3 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 11216029 = 4206011) B4206011
theorem B14954705 : Blo 1967435 14954705 := bstep (se 2 (by rfl) ⟨5608014, by rfl⟩ : syracuseStep 14954705 = 11216029) B11216029
theorem B9969803 : Blo 1967435 9969803 := bstep (se 1 (by rfl) ⟨7477352, by rfl⟩ : syracuseStep 9969803 = 14954705) B14954705
theorem B6646535 : Blo 1967435 6646535 := bstep (se 1 (by rfl) ⟨4984901, by rfl⟩ : syracuseStep 6646535 = 9969803) B9969803
theorem B4431023 : Blo 1967435 4431023 := bstep (se 1 (by rfl) ⟨3323267, by rfl⟩ : syracuseStep 4431023 = 6646535) B6646535
theorem B2954015 : Blo 1967435 2954015 := bstep (se 1 (by rfl) ⟨2215511, by rfl⟩ : syracuseStep 2954015 = 4431023) B4431023
theorem B1969343 : Blo 1967435 1969343 := bstep (se 1 (by rfl) ⟨1477007, by rfl⟩ : syracuseStep 1969343 = 2954015) B2954015
theorem B2954021 : Blo 1967435 2954021 := bbase (se 4 (by rfl) ⟨276939, by rfl⟩ : syracuseStep 2954021 = 553879) (by norm_num)
theorem B1969347 : Blo 1967435 1969347 := bstep (se 1 (by rfl) ⟨1477010, by rfl⟩ : syracuseStep 1969347 = 2954021) B2954021
theorem B2492461 : Blo 1967435 2492461 := bbase (se 3 (by rfl) ⟨467336, by rfl⟩ : syracuseStep 2492461 = 934673) (by norm_num)
theorem B3323281 : Blo 1967435 3323281 := bstep (se 2 (by rfl) ⟨1246230, by rfl⟩ : syracuseStep 3323281 = 2492461) B2492461
theorem B4431041 : Blo 1967435 4431041 := bstep (se 2 (by rfl) ⟨1661640, by rfl⟩ : syracuseStep 4431041 = 3323281) B3323281
theorem B2954027 : Blo 1967435 2954027 := bstep (se 1 (by rfl) ⟨2215520, by rfl⟩ : syracuseStep 2954027 = 4431041) B4431041
theorem B1969351 : Blo 1967435 1969351 := bstep (se 1 (by rfl) ⟨1477013, by rfl⟩ : syracuseStep 1969351 = 2954027) B2954027
theorem B2215525 : Blo 1967435 2215525 := bbase (se 4 (by rfl) ⟨207705, by rfl⟩ : syracuseStep 2215525 = 415411) (by norm_num)
theorem B2954033 : Blo 1967435 2954033 := bstep (se 2 (by rfl) ⟨1107762, by rfl⟩ : syracuseStep 2954033 = 2215525) B2215525
theorem B1969355 : Blo 1967435 1969355 := bstep (se 1 (by rfl) ⟨1477016, by rfl⟩ : syracuseStep 1969355 = 2954033) B2954033
theorem B17966069 : Blo 1967435 17966069 := bbase (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) (by norm_num)
theorem B11977379 : Blo 1967435 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B7984919 : Blo 1967435 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B5323279 : Blo 1967435 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B7097705 : Blo 1967435 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B4731803 : Blo 1967435 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B3154535 : Blo 1967435 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B2103023 : Blo 1967435 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B5608061 : Blo 1967435 5608061 := bstep (se 3 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 5608061 = 2103023) B2103023
theorem B3738707 : Blo 1967435 3738707 := bstep (se 1 (by rfl) ⟨2804030, by rfl⟩ : syracuseStep 3738707 = 5608061) B5608061
theorem B2492471 : Blo 1967435 2492471 := bstep (se 1 (by rfl) ⟨1869353, by rfl⟩ : syracuseStep 2492471 = 3738707) B3738707
theorem B6646589 : Blo 1967435 6646589 := bstep (se 3 (by rfl) ⟨1246235, by rfl⟩ : syracuseStep 6646589 = 2492471) B2492471
theorem B4431059 : Blo 1967435 4431059 := bstep (se 1 (by rfl) ⟨3323294, by rfl⟩ : syracuseStep 4431059 = 6646589) B6646589
theorem B2954039 : Blo 1967435 2954039 := bstep (se 1 (by rfl) ⟨2215529, by rfl⟩ : syracuseStep 2954039 = 4431059) B4431059
theorem B1969359 : Blo 1967435 1969359 := bstep (se 1 (by rfl) ⟨1477019, by rfl⟩ : syracuseStep 1969359 = 2954039) B2954039
theorem B2954045 : Blo 1967435 2954045 := bbase (se 3 (by rfl) ⟨553883, by rfl⟩ : syracuseStep 2954045 = 1107767) (by norm_num)
theorem B1969363 : Blo 1967435 1969363 := bstep (se 1 (by rfl) ⟨1477022, by rfl⟩ : syracuseStep 1969363 = 2954045) B2954045
theorem B4431077 : Blo 1967435 4431077 := bbase (se 4 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 4431077 = 830827) (by norm_num)
theorem B2954051 : Blo 1967435 2954051 := bstep (se 1 (by rfl) ⟨2215538, by rfl⟩ : syracuseStep 2954051 = 4431077) B4431077
theorem B1969367 : Blo 1967435 1969367 := bstep (se 1 (by rfl) ⟨1477025, by rfl⟩ : syracuseStep 1969367 = 2954051) B2954051
theorem B4984973 : Blo 1967435 4984973 := bbase (se 3 (by rfl) ⟨934682, by rfl⟩ : syracuseStep 4984973 = 1869365) (by norm_num)
theorem B3323315 : Blo 1967435 3323315 := bstep (se 1 (by rfl) ⟨2492486, by rfl⟩ : syracuseStep 3323315 = 4984973) B4984973
theorem B2215543 : Blo 1967435 2215543 := bstep (se 1 (by rfl) ⟨1661657, by rfl⟩ : syracuseStep 2215543 = 3323315) B3323315
theorem B2954057 : Blo 1967435 2954057 := bstep (se 2 (by rfl) ⟨1107771, by rfl⟩ : syracuseStep 2954057 = 2215543) B2215543
theorem B1969371 : Blo 1967435 1969371 := bstep (se 1 (by rfl) ⟨1477028, by rfl⟩ : syracuseStep 1969371 = 2954057) B2954057
theorem B2804053 : Blo 1967435 2804053 := bbase (se 10 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 2804053 = 8215) (by norm_num)
theorem B3738737 : Blo 1967435 3738737 := bstep (se 2 (by rfl) ⟨1402026, by rfl⟩ : syracuseStep 3738737 = 2804053) B2804053
theorem B9969965 : Blo 1967435 9969965 := bstep (se 3 (by rfl) ⟨1869368, by rfl⟩ : syracuseStep 9969965 = 3738737) B3738737
theorem B6646643 : Blo 1967435 6646643 := bstep (se 1 (by rfl) ⟨4984982, by rfl⟩ : syracuseStep 6646643 = 9969965) B9969965
theorem B4431095 : Blo 1967435 4431095 := bstep (se 1 (by rfl) ⟨3323321, by rfl⟩ : syracuseStep 4431095 = 6646643) B6646643
theorem B2954063 : Blo 1967435 2954063 := bstep (se 1 (by rfl) ⟨2215547, by rfl⟩ : syracuseStep 2954063 = 4431095) B4431095
theorem B1969375 : Blo 1967435 1969375 := bstep (se 1 (by rfl) ⟨1477031, by rfl⟩ : syracuseStep 1969375 = 2954063) B2954063
theorem B2954069 : Blo 1967435 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B1969379 : Blo 1967435 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B3154573 : Blo 1967435 3154573 := bbase (se 3 (by rfl) ⟨591482, by rfl⟩ : syracuseStep 3154573 = 1182965) (by norm_num)
theorem B4206097 : Blo 1967435 4206097 := bstep (se 2 (by rfl) ⟨1577286, by rfl⟩ : syracuseStep 4206097 = 3154573) B3154573
theorem B5608129 : Blo 1967435 5608129 := bstep (se 2 (by rfl) ⟨2103048, by rfl⟩ : syracuseStep 5608129 = 4206097) B4206097
theorem B7477505 : Blo 1967435 7477505 := bstep (se 2 (by rfl) ⟨2804064, by rfl⟩ : syracuseStep 7477505 = 5608129) B5608129
theorem B4985003 : Blo 1967435 4985003 := bstep (se 1 (by rfl) ⟨3738752, by rfl⟩ : syracuseStep 4985003 = 7477505) B7477505
theorem B3323335 : Blo 1967435 3323335 := bstep (se 1 (by rfl) ⟨2492501, by rfl⟩ : syracuseStep 3323335 = 4985003) B4985003
theorem B4431113 : Blo 1967435 4431113 := bstep (se 2 (by rfl) ⟨1661667, by rfl⟩ : syracuseStep 4431113 = 3323335) B3323335
theorem B2954075 : Blo 1967435 2954075 := bstep (se 1 (by rfl) ⟨2215556, by rfl⟩ : syracuseStep 2954075 = 4431113) B4431113
theorem B1969383 : Blo 1967435 1969383 := bstep (se 1 (by rfl) ⟨1477037, by rfl⟩ : syracuseStep 1969383 = 2954075) B2954075
theorem B2215561 : Blo 1967435 2215561 := bbase (se 2 (by rfl) ⟨830835, by rfl⟩ : syracuseStep 2215561 = 1661671) (by norm_num)
theorem B2954081 : Blo 1967435 2954081 := bstep (se 2 (by rfl) ⟨1107780, by rfl⟩ : syracuseStep 2954081 = 2215561) B2215561
theorem B1969387 : Blo 1967435 1969387 := bstep (se 1 (by rfl) ⟨1477040, by rfl⟩ : syracuseStep 1969387 = 2954081) B2954081
theorem B7985045 : Blo 1967435 7985045 := bbase (se 6 (by rfl) ⟨187149, by rfl⟩ : syracuseStep 7985045 = 374299) (by norm_num)
theorem B5323363 : Blo 1967435 5323363 := bstep (se 1 (by rfl) ⟨3992522, by rfl⟩ : syracuseStep 5323363 = 7985045) B7985045
theorem B28391269 : Blo 1967435 28391269 := bstep (se 4 (by rfl) ⟨2661681, by rfl⟩ : syracuseStep 28391269 = 5323363) B5323363
theorem B37855025 : Blo 1967435 37855025 := bstep (se 2 (by rfl) ⟨14195634, by rfl⟩ : syracuseStep 37855025 = 28391269) B28391269
theorem B25236683 : Blo 1967435 25236683 := bstep (se 1 (by rfl) ⟨18927512, by rfl⟩ : syracuseStep 25236683 = 37855025) B37855025
theorem B16824455 : Blo 1967435 16824455 := bstep (se 1 (by rfl) ⟨12618341, by rfl⟩ : syracuseStep 16824455 = 25236683) B25236683
theorem B11216303 : Blo 1967435 11216303 := bstep (se 1 (by rfl) ⟨8412227, by rfl⟩ : syracuseStep 11216303 = 16824455) B16824455
theorem B7477535 : Blo 1967435 7477535 := bstep (se 1 (by rfl) ⟨5608151, by rfl⟩ : syracuseStep 7477535 = 11216303) B11216303
theorem B4985023 : Blo 1967435 4985023 := bstep (se 1 (by rfl) ⟨3738767, by rfl⟩ : syracuseStep 4985023 = 7477535) B7477535
theorem B6646697 : Blo 1967435 6646697 := bstep (se 2 (by rfl) ⟨2492511, by rfl⟩ : syracuseStep 6646697 = 4985023) B4985023
theorem B4431131 : Blo 1967435 4431131 := bstep (se 1 (by rfl) ⟨3323348, by rfl⟩ : syracuseStep 4431131 = 6646697) B6646697
theorem B2954087 : Blo 1967435 2954087 := bstep (se 1 (by rfl) ⟨2215565, by rfl⟩ : syracuseStep 2954087 = 4431131) B4431131
theorem B1969391 : Blo 1967435 1969391 := bstep (se 1 (by rfl) ⟨1477043, by rfl⟩ : syracuseStep 1969391 = 2954087) B2954087
theorem B2954093 : Blo 1967435 2954093 := bbase (se 3 (by rfl) ⟨553892, by rfl⟩ : syracuseStep 2954093 = 1107785) (by norm_num)
theorem B1969395 : Blo 1967435 1969395 := bstep (se 1 (by rfl) ⟨1477046, by rfl⟩ : syracuseStep 1969395 = 2954093) B2954093
theorem B4431149 : Blo 1967435 4431149 := bbase (se 3 (by rfl) ⟨830840, by rfl⟩ : syracuseStep 4431149 = 1661681) (by norm_num)
theorem B2954099 : Blo 1967435 2954099 := bstep (se 1 (by rfl) ⟨2215574, by rfl⟩ : syracuseStep 2954099 = 4431149) B4431149
theorem B1969399 : Blo 1967435 1969399 := bstep (se 1 (by rfl) ⟨1477049, by rfl⟩ : syracuseStep 1969399 = 2954099) B2954099
theorem B5469653 : Blo 1967435 5469653 := bbase (se 7 (by rfl) ⟨64097, by rfl⟩ : syracuseStep 5469653 = 128195) (by norm_num)
theorem B14585741 : Blo 1967435 14585741 := bstep (se 3 (by rfl) ⟨2734826, by rfl⟩ : syracuseStep 14585741 = 5469653) B5469653
theorem B9723827 : Blo 1967435 9723827 := bstep (se 1 (by rfl) ⟨7292870, by rfl⟩ : syracuseStep 9723827 = 14585741) B14585741
theorem B6482551 : Blo 1967435 6482551 := bstep (se 1 (by rfl) ⟨4861913, by rfl⟩ : syracuseStep 6482551 = 9723827) B9723827
theorem B8643401 : Blo 1967435 8643401 := bstep (se 2 (by rfl) ⟨3241275, by rfl⟩ : syracuseStep 8643401 = 6482551) B6482551
theorem B5762267 : Blo 1967435 5762267 := bstep (se 1 (by rfl) ⟨4321700, by rfl⟩ : syracuseStep 5762267 = 8643401) B8643401
theorem B3841511 : Blo 1967435 3841511 := bstep (se 1 (by rfl) ⟨2881133, by rfl⟩ : syracuseStep 3841511 = 5762267) B5762267
theorem B10244029 : Blo 1967435 10244029 := bstep (se 3 (by rfl) ⟨1920755, by rfl⟩ : syracuseStep 10244029 = 3841511) B3841511
theorem B13658705 : Blo 1967435 13658705 := bstep (se 2 (by rfl) ⟨5122014, by rfl⟩ : syracuseStep 13658705 = 10244029) B10244029
theorem B9105803 : Blo 1967435 9105803 := bstep (se 1 (by rfl) ⟨6829352, by rfl⟩ : syracuseStep 9105803 = 13658705) B13658705
theorem B6070535 : Blo 1967435 6070535 := bstep (se 1 (by rfl) ⟨4552901, by rfl⟩ : syracuseStep 6070535 = 9105803) B9105803
theorem B4047023 : Blo 1967435 4047023 := bstep (se 1 (by rfl) ⟨3035267, by rfl⟩ : syracuseStep 4047023 = 6070535) B6070535
theorem B10792061 : Blo 1967435 10792061 := bstep (se 3 (by rfl) ⟨2023511, by rfl⟩ : syracuseStep 10792061 = 4047023) B4047023
theorem B7194707 : Blo 1967435 7194707 := bstep (se 1 (by rfl) ⟨5396030, by rfl⟩ : syracuseStep 7194707 = 10792061) B10792061
theorem B4796471 : Blo 1967435 4796471 := bstep (se 1 (by rfl) ⟨3597353, by rfl⟩ : syracuseStep 4796471 = 7194707) B7194707
theorem B3197647 : Blo 1967435 3197647 := bstep (se 1 (by rfl) ⟨2398235, by rfl⟩ : syracuseStep 3197647 = 4796471) B4796471
theorem B4263529 : Blo 1967435 4263529 := bstep (se 2 (by rfl) ⟨1598823, by rfl⟩ : syracuseStep 4263529 = 3197647) B3197647
theorem B5684705 : Blo 1967435 5684705 := bstep (se 2 (by rfl) ⟨2131764, by rfl⟩ : syracuseStep 5684705 = 4263529) B4263529
theorem B3789803 : Blo 1967435 3789803 := bstep (se 1 (by rfl) ⟨2842352, by rfl⟩ : syracuseStep 3789803 = 5684705) B5684705
theorem B2526535 : Blo 1967435 2526535 := bstep (se 1 (by rfl) ⟨1894901, by rfl⟩ : syracuseStep 2526535 = 3789803) B3789803
theorem B3368713 : Blo 1967435 3368713 := bstep (se 2 (by rfl) ⟨1263267, by rfl⟩ : syracuseStep 3368713 = 2526535) B2526535
theorem B4491617 : Blo 1967435 4491617 := bstep (se 2 (by rfl) ⟨1684356, by rfl⟩ : syracuseStep 4491617 = 3368713) B3368713
theorem B11977645 : Blo 1967435 11977645 := bstep (se 3 (by rfl) ⟨2245808, by rfl⟩ : syracuseStep 11977645 = 4491617) B4491617
theorem B15970193 : Blo 1967435 15970193 := bstep (se 2 (by rfl) ⟨5988822, by rfl⟩ : syracuseStep 15970193 = 11977645) B11977645
theorem B10646795 : Blo 1967435 10646795 := bstep (se 1 (by rfl) ⟨7985096, by rfl⟩ : syracuseStep 10646795 = 15970193) B15970193
theorem B7097863 : Blo 1967435 7097863 := bstep (se 1 (by rfl) ⟨5323397, by rfl⟩ : syracuseStep 7097863 = 10646795) B10646795
theorem B9463817 : Blo 1967435 9463817 := bstep (se 2 (by rfl) ⟨3548931, by rfl⟩ : syracuseStep 9463817 = 7097863) B7097863
theorem B6309211 : Blo 1967435 6309211 := bstep (se 1 (by rfl) ⟨4731908, by rfl⟩ : syracuseStep 6309211 = 9463817) B9463817
theorem B8412281 : Blo 1967435 8412281 := bstep (se 2 (by rfl) ⟨3154605, by rfl⟩ : syracuseStep 8412281 = 6309211) B6309211
theorem B5608187 : Blo 1967435 5608187 := bstep (se 1 (by rfl) ⟨4206140, by rfl⟩ : syracuseStep 5608187 = 8412281) B8412281
theorem B3738791 : Blo 1967435 3738791 := bstep (se 1 (by rfl) ⟨2804093, by rfl⟩ : syracuseStep 3738791 = 5608187) B5608187
theorem B2492527 : Blo 1967435 2492527 := bstep (se 1 (by rfl) ⟨1869395, by rfl⟩ : syracuseStep 2492527 = 3738791) B3738791
theorem B3323369 : Blo 1967435 3323369 := bstep (se 2 (by rfl) ⟨1246263, by rfl⟩ : syracuseStep 3323369 = 2492527) B2492527
theorem B2215579 : Blo 1967435 2215579 := bstep (se 1 (by rfl) ⟨1661684, by rfl⟩ : syracuseStep 2215579 = 3323369) B3323369
theorem B2954105 : Blo 1967435 2954105 := bstep (se 2 (by rfl) ⟨1107789, by rfl⟩ : syracuseStep 2954105 = 2215579) B2215579
theorem B1969403 : Blo 1967435 1969403 := bstep (se 1 (by rfl) ⟨1477052, by rfl⟩ : syracuseStep 1969403 = 2954105) B2954105
theorem B11369429 : Blo 1967435 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B7579619 : Blo 1967435 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B5053079 : Blo 1967435 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B3368719 : Blo 1967435 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B4491625 : Blo 1967435 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B5988833 : Blo 1967435 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B3992555 : Blo 1967435 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B2661703 : Blo 1967435 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B14195749 : Blo 1967435 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B18927665 : Blo 1967435 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B12618443 : Blo 1967435 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B33649181 : Blo 1967435 33649181 := bstep (se 3 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 33649181 = 12618443) B12618443
theorem B22432787 : Blo 1967435 22432787 := bstep (se 1 (by rfl) ⟨16824590, by rfl⟩ : syracuseStep 22432787 = 33649181) B33649181
theorem B14955191 : Blo 1967435 14955191 := bstep (se 1 (by rfl) ⟨11216393, by rfl⟩ : syracuseStep 14955191 = 22432787) B22432787
theorem B9970127 : Blo 1967435 9970127 := bstep (se 1 (by rfl) ⟨7477595, by rfl⟩ : syracuseStep 9970127 = 14955191) B14955191
theorem B6646751 : Blo 1967435 6646751 := bstep (se 1 (by rfl) ⟨4985063, by rfl⟩ : syracuseStep 6646751 = 9970127) B9970127
theorem B4431167 : Blo 1967435 4431167 := bstep (se 1 (by rfl) ⟨3323375, by rfl⟩ : syracuseStep 4431167 = 6646751) B6646751
theorem B2954111 : Blo 1967435 2954111 := bstep (se 1 (by rfl) ⟨2215583, by rfl⟩ : syracuseStep 2954111 = 4431167) B4431167
theorem B1969407 : Blo 1967435 1969407 := bstep (se 1 (by rfl) ⟨1477055, by rfl⟩ : syracuseStep 1969407 = 2954111) B2954111
theorem B2954117 : Blo 1967435 2954117 := bbase (se 4 (by rfl) ⟨276948, by rfl⟩ : syracuseStep 2954117 = 553897) (by norm_num)
theorem B1969411 : Blo 1967435 1969411 := bstep (se 1 (by rfl) ⟨1477058, by rfl⟩ : syracuseStep 1969411 = 2954117) B2954117
theorem B3323389 : Blo 1967435 3323389 := bbase (se 3 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 3323389 = 1246271) (by norm_num)
theorem B4431185 : Blo 1967435 4431185 := bstep (se 2 (by rfl) ⟨1661694, by rfl⟩ : syracuseStep 4431185 = 3323389) B3323389
theorem B2954123 : Blo 1967435 2954123 := bstep (se 1 (by rfl) ⟨2215592, by rfl⟩ : syracuseStep 2954123 = 4431185) B4431185
theorem B1969415 : Blo 1967435 1969415 := bstep (se 1 (by rfl) ⟨1477061, by rfl⟩ : syracuseStep 1969415 = 2954123) B2954123
theorem B2215597 : Blo 1967435 2215597 := bbase (se 3 (by rfl) ⟨415424, by rfl⟩ : syracuseStep 2215597 = 830849) (by norm_num)
theorem B2954129 : Blo 1967435 2954129 := bstep (se 2 (by rfl) ⟨1107798, by rfl⟩ : syracuseStep 2954129 = 2215597) B2215597
theorem B1969419 : Blo 1967435 1969419 := bstep (se 1 (by rfl) ⟨1477064, by rfl⟩ : syracuseStep 1969419 = 2954129) B2954129
theorem B6646805 : Blo 1967435 6646805 := bbase (se 6 (by rfl) ⟨155784, by rfl⟩ : syracuseStep 6646805 = 311569) (by norm_num)
theorem B4431203 : Blo 1967435 4431203 := bstep (se 1 (by rfl) ⟨3323402, by rfl⟩ : syracuseStep 4431203 = 6646805) B6646805
theorem B2954135 : Blo 1967435 2954135 := bstep (se 1 (by rfl) ⟨2215601, by rfl⟩ : syracuseStep 2954135 = 4431203) B4431203
theorem B1969423 : Blo 1967435 1969423 := bstep (se 1 (by rfl) ⟨1477067, by rfl⟩ : syracuseStep 1969423 = 2954135) B2954135
theorem B2954141 : Blo 1967435 2954141 := bbase (se 3 (by rfl) ⟨553901, by rfl⟩ : syracuseStep 2954141 = 1107803) (by norm_num)
theorem B1969427 : Blo 1967435 1969427 := bstep (se 1 (by rfl) ⟨1477070, by rfl⟩ : syracuseStep 1969427 = 2954141) B2954141
theorem B4431221 : Blo 1967435 4431221 := bbase (se 5 (by rfl) ⟨207713, by rfl⟩ : syracuseStep 4431221 = 415427) (by norm_num)
theorem B2954147 : Blo 1967435 2954147 := bstep (se 1 (by rfl) ⟨2215610, by rfl⟩ : syracuseStep 2954147 = 4431221) B4431221
theorem B1969431 : Blo 1967435 1969431 := bstep (se 1 (by rfl) ⟨1477073, by rfl⟩ : syracuseStep 1969431 = 2954147) B2954147
theorem B9593093 : Blo 1967435 9593093 := bbase (se 4 (by rfl) ⟨899352, by rfl⟩ : syracuseStep 9593093 = 1798705) (by norm_num)
theorem B25581581 : Blo 1967435 25581581 := bstep (se 3 (by rfl) ⟨4796546, by rfl⟩ : syracuseStep 25581581 = 9593093) B9593093
theorem B17054387 : Blo 1967435 17054387 := bstep (se 1 (by rfl) ⟨12790790, by rfl⟩ : syracuseStep 17054387 = 25581581) B25581581
theorem B11369591 : Blo 1967435 11369591 := bstep (se 1 (by rfl) ⟨8527193, by rfl⟩ : syracuseStep 11369591 = 17054387) B17054387
theorem B7579727 : Blo 1967435 7579727 := bstep (se 1 (by rfl) ⟨5684795, by rfl⟩ : syracuseStep 7579727 = 11369591) B11369591
theorem B5053151 : Blo 1967435 5053151 := bstep (se 1 (by rfl) ⟨3789863, by rfl⟩ : syracuseStep 5053151 = 7579727) B7579727
theorem B13475069 : Blo 1967435 13475069 := bstep (se 3 (by rfl) ⟨2526575, by rfl⟩ : syracuseStep 13475069 = 5053151) B5053151
theorem B8983379 : Blo 1967435 8983379 := bstep (se 1 (by rfl) ⟨6737534, by rfl⟩ : syracuseStep 8983379 = 13475069) B13475069
theorem B5988919 : Blo 1967435 5988919 := bstep (se 1 (by rfl) ⟨4491689, by rfl⟩ : syracuseStep 5988919 = 8983379) B8983379
theorem B7985225 : Blo 1967435 7985225 := bstep (se 2 (by rfl) ⟨2994459, by rfl⟩ : syracuseStep 7985225 = 5988919) B5988919
theorem B5323483 : Blo 1967435 5323483 := bstep (se 1 (by rfl) ⟨3992612, by rfl⟩ : syracuseStep 5323483 = 7985225) B7985225
theorem B7097977 : Blo 1967435 7097977 := bstep (se 2 (by rfl) ⟨2661741, by rfl⟩ : syracuseStep 7097977 = 5323483) B5323483
theorem B9463969 : Blo 1967435 9463969 := bstep (se 2 (by rfl) ⟨3548988, by rfl⟩ : syracuseStep 9463969 = 7097977) B7097977
theorem B12618625 : Blo 1967435 12618625 := bstep (se 2 (by rfl) ⟨4731984, by rfl⟩ : syracuseStep 12618625 = 9463969) B9463969
theorem B16824833 : Blo 1967435 16824833 := bstep (se 2 (by rfl) ⟨6309312, by rfl⟩ : syracuseStep 16824833 = 12618625) B12618625
theorem B11216555 : Blo 1967435 11216555 := bstep (se 1 (by rfl) ⟨8412416, by rfl⟩ : syracuseStep 11216555 = 16824833) B16824833
theorem B7477703 : Blo 1967435 7477703 := bstep (se 1 (by rfl) ⟨5608277, by rfl⟩ : syracuseStep 7477703 = 11216555) B11216555
theorem B4985135 : Blo 1967435 4985135 := bstep (se 1 (by rfl) ⟨3738851, by rfl⟩ : syracuseStep 4985135 = 7477703) B7477703
theorem B3323423 : Blo 1967435 3323423 := bstep (se 1 (by rfl) ⟨2492567, by rfl⟩ : syracuseStep 3323423 = 4985135) B4985135
theorem B2215615 : Blo 1967435 2215615 := bstep (se 1 (by rfl) ⟨1661711, by rfl⟩ : syracuseStep 2215615 = 3323423) B3323423
theorem B2954153 : Blo 1967435 2954153 := bstep (se 2 (by rfl) ⟨1107807, by rfl⟩ : syracuseStep 2954153 = 2215615) B2215615
theorem B1969435 : Blo 1967435 1969435 := bstep (se 1 (by rfl) ⟨1477076, by rfl⟩ : syracuseStep 1969435 = 2954153) B2954153
theorem C0 (j : ℕ) (h1 : 491858 ≤ j) (h2 : j ≤ 492358) : Blo 1967435 (4 * j + 3) := by
  interval_cases j
  · exact B1967435
  · exact B1967439
  · exact B1967443
  · exact B1967447
  · exact B1967451
  · exact B1967455
  · exact B1967459
  · exact B1967463
  · exact B1967467
  · exact B1967471
  · exact B1967475
  · exact B1967479
  · exact B1967483
  · exact B1967487
  · exact B1967491
  · exact B1967495
  · exact B1967499
  · exact B1967503
  · exact B1967507
  · exact B1967511
  · exact B1967515
  · exact B1967519
  · exact B1967523
  · exact B1967527
  · exact B1967531
  · exact B1967535
  · exact B1967539
  · exact B1967543
  · exact B1967547
  · exact B1967551
  · exact B1967555
  · exact B1967559
  · exact B1967563
  · exact B1967567
  · exact B1967571
  · exact B1967575
  · exact B1967579
  · exact B1967583
  · exact B1967587
  · exact B1967591
  · exact B1967595
  · exact B1967599
  · exact B1967603
  · exact B1967607
  · exact B1967611
  · exact B1967615
  · exact B1967619
  · exact B1967623
  · exact B1967627
  · exact B1967631
  · exact B1967635
  · exact B1967639
  · exact B1967643
  · exact B1967647
  · exact B1967651
  · exact B1967655
  · exact B1967659
  · exact B1967663
  · exact B1967667
  · exact B1967671
  · exact B1967675
  · exact B1967679
  · exact B1967683
  · exact B1967687
  · exact B1967691
  · exact B1967695
  · exact B1967699
  · exact B1967703
  · exact B1967707
  · exact B1967711
  · exact B1967715
  · exact B1967719
  · exact B1967723
  · exact B1967727
  · exact B1967731
  · exact B1967735
  · exact B1967739
  · exact B1967743
  · exact B1967747
  · exact B1967751
  · exact B1967755
  · exact B1967759
  · exact B1967763
  · exact B1967767
  · exact B1967771
  · exact B1967775
  · exact B1967779
  · exact B1967783
  · exact B1967787
  · exact B1967791
  · exact B1967795
  · exact B1967799
  · exact B1967803
  · exact B1967807
  · exact B1967811
  · exact B1967815
  · exact B1967819
  · exact B1967823
  · exact B1967827
  · exact B1967831
  · exact B1967835
  · exact B1967839
  · exact B1967843
  · exact B1967847
  · exact B1967851
  · exact B1967855
  · exact B1967859
  · exact B1967863
  · exact B1967867
  · exact B1967871
  · exact B1967875
  · exact B1967879
  · exact B1967883
  · exact B1967887
  · exact B1967891
  · exact B1967895
  · exact B1967899
  · exact B1967903
  · exact B1967907
  · exact B1967911
  · exact B1967915
  · exact B1967919
  · exact B1967923
  · exact B1967927
  · exact B1967931
  · exact B1967935
  · exact B1967939
  · exact B1967943
  · exact B1967947
  · exact B1967951
  · exact B1967955
  · exact B1967959
  · exact B1967963
  · exact B1967967
  · exact B1967971
  · exact B1967975
  · exact B1967979
  · exact B1967983
  · exact B1967987
  · exact B1967991
  · exact B1967995
  · exact B1967999
  · exact B1968003
  · exact B1968007
  · exact B1968011
  · exact B1968015
  · exact B1968019
  · exact B1968023
  · exact B1968027
  · exact B1968031
  · exact B1968035
  · exact B1968039
  · exact B1968043
  · exact B1968047
  · exact B1968051
  · exact B1968055
  · exact B1968059
  · exact B1968063
  · exact B1968067
  · exact B1968071
  · exact B1968075
  · exact B1968079
  · exact B1968083
  · exact B1968087
  · exact B1968091
  · exact B1968095
  · exact B1968099
  · exact B1968103
  · exact B1968107
  · exact B1968111
  · exact B1968115
  · exact B1968119
  · exact B1968123
  · exact B1968127
  · exact B1968131
  · exact B1968135
  · exact B1968139
  · exact B1968143
  · exact B1968147
  · exact B1968151
  · exact B1968155
  · exact B1968159
  · exact B1968163
  · exact B1968167
  · exact B1968171
  · exact B1968175
  · exact B1968179
  · exact B1968183
  · exact B1968187
  · exact B1968191
  · exact B1968195
  · exact B1968199
  · exact B1968203
  · exact B1968207
  · exact B1968211
  · exact B1968215
  · exact B1968219
  · exact B1968223
  · exact B1968227
  · exact B1968231
  · exact B1968235
  · exact B1968239
  · exact B1968243
  · exact B1968247
  · exact B1968251
  · exact B1968255
  · exact B1968259
  · exact B1968263
  · exact B1968267
  · exact B1968271
  · exact B1968275
  · exact B1968279
  · exact B1968283
  · exact B1968287
  · exact B1968291
  · exact B1968295
  · exact B1968299
  · exact B1968303
  · exact B1968307
  · exact B1968311
  · exact B1968315
  · exact B1968319
  · exact B1968323
  · exact B1968327
  · exact B1968331
  · exact B1968335
  · exact B1968339
  · exact B1968343
  · exact B1968347
  · exact B1968351
  · exact B1968355
  · exact B1968359
  · exact B1968363
  · exact B1968367
  · exact B1968371
  · exact B1968375
  · exact B1968379
  · exact B1968383
  · exact B1968387
  · exact B1968391
  · exact B1968395
  · exact B1968399
  · exact B1968403
  · exact B1968407
  · exact B1968411
  · exact B1968415
  · exact B1968419
  · exact B1968423
  · exact B1968427
  · exact B1968431
  · exact B1968435
  · exact B1968439
  · exact B1968443
  · exact B1968447
  · exact B1968451
  · exact B1968455
  · exact B1968459
  · exact B1968463
  · exact B1968467
  · exact B1968471
  · exact B1968475
  · exact B1968479
  · exact B1968483
  · exact B1968487
  · exact B1968491
  · exact B1968495
  · exact B1968499
  · exact B1968503
  · exact B1968507
  · exact B1968511
  · exact B1968515
  · exact B1968519
  · exact B1968523
  · exact B1968527
  · exact B1968531
  · exact B1968535
  · exact B1968539
  · exact B1968543
  · exact B1968547
  · exact B1968551
  · exact B1968555
  · exact B1968559
  · exact B1968563
  · exact B1968567
  · exact B1968571
  · exact B1968575
  · exact B1968579
  · exact B1968583
  · exact B1968587
  · exact B1968591
  · exact B1968595
  · exact B1968599
  · exact B1968603
  · exact B1968607
  · exact B1968611
  · exact B1968615
  · exact B1968619
  · exact B1968623
  · exact B1968627
  · exact B1968631
  · exact B1968635
  · exact B1968639
  · exact B1968643
  · exact B1968647
  · exact B1968651
  · exact B1968655
  · exact B1968659
  · exact B1968663
  · exact B1968667
  · exact B1968671
  · exact B1968675
  · exact B1968679
  · exact B1968683
  · exact B1968687
  · exact B1968691
  · exact B1968695
  · exact B1968699
  · exact B1968703
  · exact B1968707
  · exact B1968711
  · exact B1968715
  · exact B1968719
  · exact B1968723
  · exact B1968727
  · exact B1968731
  · exact B1968735
  · exact B1968739
  · exact B1968743
  · exact B1968747
  · exact B1968751
  · exact B1968755
  · exact B1968759
  · exact B1968763
  · exact B1968767
  · exact B1968771
  · exact B1968775
  · exact B1968779
  · exact B1968783
  · exact B1968787
  · exact B1968791
  · exact B1968795
  · exact B1968799
  · exact B1968803
  · exact B1968807
  · exact B1968811
  · exact B1968815
  · exact B1968819
  · exact B1968823
  · exact B1968827
  · exact B1968831
  · exact B1968835
  · exact B1968839
  · exact B1968843
  · exact B1968847
  · exact B1968851
  · exact B1968855
  · exact B1968859
  · exact B1968863
  · exact B1968867
  · exact B1968871
  · exact B1968875
  · exact B1968879
  · exact B1968883
  · exact B1968887
  · exact B1968891
  · exact B1968895
  · exact B1968899
  · exact B1968903
  · exact B1968907
  · exact B1968911
  · exact B1968915
  · exact B1968919
  · exact B1968923
  · exact B1968927
  · exact B1968931
  · exact B1968935
  · exact B1968939
  · exact B1968943
  · exact B1968947
  · exact B1968951
  · exact B1968955
  · exact B1968959
  · exact B1968963
  · exact B1968967
  · exact B1968971
  · exact B1968975
  · exact B1968979
  · exact B1968983
  · exact B1968987
  · exact B1968991
  · exact B1968995
  · exact B1968999
  · exact B1969003
  · exact B1969007
  · exact B1969011
  · exact B1969015
  · exact B1969019
  · exact B1969023
  · exact B1969027
  · exact B1969031
  · exact B1969035
  · exact B1969039
  · exact B1969043
  · exact B1969047
  · exact B1969051
  · exact B1969055
  · exact B1969059
  · exact B1969063
  · exact B1969067
  · exact B1969071
  · exact B1969075
  · exact B1969079
  · exact B1969083
  · exact B1969087
  · exact B1969091
  · exact B1969095
  · exact B1969099
  · exact B1969103
  · exact B1969107
  · exact B1969111
  · exact B1969115
  · exact B1969119
  · exact B1969123
  · exact B1969127
  · exact B1969131
  · exact B1969135
  · exact B1969139
  · exact B1969143
  · exact B1969147
  · exact B1969151
  · exact B1969155
  · exact B1969159
  · exact B1969163
  · exact B1969167
  · exact B1969171
  · exact B1969175
  · exact B1969179
  · exact B1969183
  · exact B1969187
  · exact B1969191
  · exact B1969195
  · exact B1969199
  · exact B1969203
  · exact B1969207
  · exact B1969211
  · exact B1969215
  · exact B1969219
  · exact B1969223
  · exact B1969227
  · exact B1969231
  · exact B1969235
  · exact B1969239
  · exact B1969243
  · exact B1969247
  · exact B1969251
  · exact B1969255
  · exact B1969259
  · exact B1969263
  · exact B1969267
  · exact B1969271
  · exact B1969275
  · exact B1969279
  · exact B1969283
  · exact B1969287
  · exact B1969291
  · exact B1969295
  · exact B1969299
  · exact B1969303
  · exact B1969307
  · exact B1969311
  · exact B1969315
  · exact B1969319
  · exact B1969323
  · exact B1969327
  · exact B1969331
  · exact B1969335
  · exact B1969339
  · exact B1969343
  · exact B1969347
  · exact B1969351
  · exact B1969355
  · exact B1969359
  · exact B1969363
  · exact B1969367
  · exact B1969371
  · exact B1969375
  · exact B1969379
  · exact B1969383
  · exact B1969387
  · exact B1969391
  · exact B1969395
  · exact B1969399
  · exact B1969403
  · exact B1969407
  · exact B1969411
  · exact B1969415
  · exact B1969419
  · exact B1969423
  · exact B1969427
  · exact B1969431
  · exact B1969435
theorem solution (m : ℕ) (hlo : 1967435 ≤ m) (hhi : m ≤ 1969435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 491858 ≤ j := by omega
    have hj2 : j ≤ 492358 := by omega
    have hb : Blo 1967435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
