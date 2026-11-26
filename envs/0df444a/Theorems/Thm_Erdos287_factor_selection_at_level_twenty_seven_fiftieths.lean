-- Prove2me | Theorems.Thm_Erdos287_factor_selection_at_level_twenty_seven_fiftieths
-- name    : Erdos287.factor_selection_at_level_twenty_seven_fiftieths
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:36:19.993497+00:00
-- url     : https://prove2.me/theorems/4d1860d1-8f37-4f68-abca-7b7bf18d4f42
-- title:
--   Factor selection at sieve level 27/50
-- statement:
--   For nonnegative box exponents summing to one, assume each nonsmooth exponent is at most 0.251. Either there is a smooth exponent at least 0.3101, some subset has sum in [0.0801, 0.3065], or exactly three exponents at least 0.0801 remain and all three are smooth and in (0.3065, 0.3101). In the last case the remaining exponent lies in [0.0697, 0.0801). The statement also checks the displayed Type I and combined Type II scale margins at level 27/50, and the Type III scale margins when the remaining exponent is at most 0.0732.
-- source:
--   Erdős #287, mixed linear upper sieve. Zheng, Simultaneous equidistribution of primes in arithmetic progressions, §8.

import Mathlib

theorem Erdos287.factor_selection_at_level_twenty_seven_fiftieths {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 1000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 3101 / 10000 ≤ x i) ∨
      (∃ J ⊆ I, 801 / 10000 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 613 / 2000) ∨
      ∃ L ⊆ I, L.card = 3 ∧
        (∀ i ∈ L, i ∈ smooth ∧ 613 / 2000 < x i ∧ x i < 3101 / 10000) ∧
        (697 / 10000 ≤ ∑ i ∈ I \ L, x i) ∧
        ((∑ i ∈ I \ L, x i) ≤ 183 / 2500 ∨
          183 / 2500 < (∑ i ∈ I \ L, x i) ∧ (∑ i ∈ I \ L, x i) < 801 / 10000)) ∧
    (∀ m r s : ℝ, 3101 / 10000 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 27 / 50 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 801 / 10000 ≤ ν → ν ≤ 613 / 2000 → 0 ≤ r → 0 ≤ s →
      r ≤ 27 / 50 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    (∀ a q r s : ℝ, a ≤ 183 / 2500 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 23 / 75 + ε → 0 ≤ s → s ≤ 7 / 30 + ε →
      a + 4 * q + 4 * r + 3 * s - 1 ≤ 1 - ε ∧
      a + 7 * q / 4 + 7 * r / 4 + 3 * s / 2 ≤ 1 - ε ∧
      a + 3 * q / 2 + 3 * r / 2 + 2 * s ≤ 1 - ε) := by sorry
