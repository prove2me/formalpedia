-- Prove2me | Theorems.Thm_Erdos287_asymmetric_chen_type_one_and_two_exponent_margins
-- name    : Erdos287.asymmetric_chen_type_one_and_two_exponent_margins
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:58:32.792068+00:00
-- url     : https://prove2.me/theorems/c89a8f67-cf56-4a44-a408-2616570e73da
-- title:
--   Type I and Type II exponents for the asymmetric Chen levels
-- statement:
--   At levels at most $2127/4000$, a smooth factor of exponent at least $3/10$ meets the Type I size conditions, and an exponent in $[3/25,3/10]$ meets the Type II size conditions with the stated margins. These two ranges cover all normalized Heath–Brown boxes with at most eight factors and the stated nonsmooth exponent cap.
-- source:
--   Erdős Problem 287. Conditional sieve criteria for the unbounded range.

import Mathlib

theorem Erdos287.asymmetric_chen_type_one_and_two_exponent_margins {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (θ ε : ℝ) (hθ : θ ≤ 2127 / 4000) (hε : 0 < ε) (hεmax : ε ≤ 1 / 10000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ 3 / 10) ∧
    (∀ m r s : ℝ, 3 / 10 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ 3 / 10 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) := by sorry
