-- Prove2me | Theorems.Thm_Erdos287_gcd_harmonic_weight_le_divisor_count
-- name    : Erdos287.gcd_harmonic_weight_le_divisor_count
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:07:38.082284+00:00
-- url     : https://prove2.me/theorems/afee9c76-736d-4a82-ab51-bc3544b8cb54
-- title:
--   Harmonic gcd bound for parameter progression weights
-- statement:
--   For any positive integer $s$ and $B\ge0$, $\sum_{1\le n\le B}\gcd(s,n)/n\le\tau(s)\sum_{1\le j\le B}1/j$, where $\tau(s)$ is the number of positive divisors of $s$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.gcd_harmonic_weight_le_divisor_count (s B : ℕ) (hs : 0 < s) :
    (∑ n ∈ Finset.Icc 1 B, (Nat.gcd s n : ℚ) / n) ≤
      (s.divisors.card : ℚ) * ∑ j ∈ Finset.Icc 1 B, (1 : ℚ) / j := by sorry
