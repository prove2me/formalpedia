-- Prove2me | Theorems.Thm_Erdos287_short_type_ii_factor_selection_at_level_547_1000
-- name    : Erdos287.short_type_ii_factor_selection_at_level_547_1000
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:13:01.843852+00:00
-- url     : https://prove2.me/theorems/8a102330-d6a5-4683-8cf6-d42a11ac3505
-- title:
--   Short Type II factor selection at sieve level 0.547
-- statement:
--   For nonnegative box exponents with sum one and nonsmooth exponents at most 0.251, either a smooth exponent is at least 0.3206 or a subproduct exponent belongs to [0.01,0.3018]. At sieve level 0.547 the stated Type I size tests hold in the first case. For a subproduct at most 0.104 the Fouvry C.4 exponent inequalities hold at caps 0.4525 and 0.0945, with slack for a small auxiliary modulus. The corrected last spectral term is dominated by a term already in the bound. The larger subproducts meet the combined Type II size tests. The formal coefficient 2/0.547 is below 11/3 and the placement ratio 8/3 is below e.
-- source:
--   Erdős #287, Fouvry, Autour du théorème de Bombieri–Vinogradov II, (C.4) and §V.2; Bombieri–Friedlander–Iwaniec, Some corrections to an old paper.

import Mathlib

theorem Erdos287.short_type_ii_factor_selection_at_level_547_1000 {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 1000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 1603 / 5000 ≤ x i) ∨
      ∃ J ⊆ I, 1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1509 / 5000) ∧
    (∀ m r s : ℝ, 1603 / 5000 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 547 / 1000 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν q r s : ℝ, 1 / 100 ≤ ν → ν ≤ 13 / 125 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 181 / 400 + ε → 0 ≤ s → s ≤ 189 / 2000 + ε →
      2 * (r + q) + s ≤ 1 - ε ∧
      5 * ν / 2 + (r + q) + 5 * s / 2 ≤ 1 - ε ∧
      5 * ν / 4 + 3 * (r + q) / 2 + 2 * s ≤ 1 - ε ∧
      5 * ν + 4 * (r + q) + 5 * s - 1 ≤ 6 * ν + 2 * (r + q) + 5 * s) ∧
    (∀ ν r s : ℝ, 13 / 125 ≤ ν → ν ≤ 1509 / 5000 → 0 ≤ r → 0 ≤ s →
      r ≤ 547 / 1000 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    2 / (547 / 1000 : ℝ) < 11 / 3 ∧ 8 / (3 : ℝ) < Real.exp 1 := by sorry
