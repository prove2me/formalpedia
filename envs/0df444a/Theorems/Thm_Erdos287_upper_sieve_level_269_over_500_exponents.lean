-- Prove2me | Theorems.Thm_Erdos287_upper_sieve_level_269_over_500_exponents
-- name    : Erdos287.upper_sieve_level_269_over_500_exponents
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:58:58.694409+00:00
-- url     : https://prove2.me/theorems/e093100e-3a2d-57d7-946b-50e5e328949d
-- title:
--   Exponent margins for the Erdős 287 upper-only sieve at level 269/500
-- statement:
--   At level 269/500, at most eight exponents summing to one, with every nonsmooth exponent at most 0.251, supply a smooth Type I variable of exponent at least 0.3075 or a single Type II variable in [0.12, 0.3075]. The specified Type I and Type II inequalities have positive slack, and the linear upper sieve coefficient 1000/269 is below 1+1359/500<1+e.
-- source:
--   Erdős #287, mixed residue upper linear sieve exponent analysis.

import Mathlib

theorem Erdos287.upper_sieve_level_269_over_500_exponents {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000) :
    let θ : ℝ := 269 / 500
    ((∃ i ∈ I, i ∈ smooth ∧ 123 / 400 ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ 123 / 400) ∧
    (∀ m r s : ℝ, 123 / 400 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ 123 / 400 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) ∧
    2 / θ < 1 + (1359 / 500 : ℝ) ∧ 1359 / 500 < Real.exp 1 := by sorry
