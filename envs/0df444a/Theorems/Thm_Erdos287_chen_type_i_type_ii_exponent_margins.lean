-- Prove2me | Theorems.Thm_Erdos287_chen_type_i_type_ii_exponent_margins
-- name    : Erdos287.chen_type_i_type_ii_exponent_margins
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:28:56.06397+00:00
-- url     : https://prove2.me/theorems/84fb8b42-61f8-4e33-abd2-365ef250e40b
-- title:
--   Type I and Type II exponent margins at level 0.5325
-- statement:
--   At level $\Theta=213/400$, the Type I scale $m\ge 0.3$ and the Type II scale $0.1\le\nu\le0.251$ satisfy the stated linear exponent margins. The dyadic factors $r,s$ range independently under upper caps, with the lower bound $r+s\ge 1/2-\varepsilon$ needed only in Type II.
-- source:
--   Erdős Problem 287 grouped Chen sieve.

import Mathlib

theorem Erdos287.chen_type_i_type_ii_exponent_margins (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000) :
    let θ : ℝ := 213 / 400
    (∀ m r s : ℝ, 3 / 10 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 1 / 10 ≤ ν → ν ≤ 251 / 1000 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) := by sorry
