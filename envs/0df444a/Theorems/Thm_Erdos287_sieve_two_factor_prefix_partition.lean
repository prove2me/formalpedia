-- Prove2me | Theorems.Thm_Erdos287_sieve_two_factor_prefix_partition
-- name    : Erdos287.sieve_two_factor_prefix_partition
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:47:32.525728+00:00
-- url     : https://prove2.me/theorems/51b7bec1-36cc-458b-a63d-25aad2cd4f3a
-- title:
--   Two-factor partition under the linear sieve prefix bounds
-- statement:
--   A list of logarithmic factor sizes partitions into two lists whose sums fit any two nonnegative capacities, provided the sum of each strict prefix plus twice the next entry fits the sum of the capacities.
-- source:
--   Erdős Problem #287 sieve reduction, Iwaniec linear sieve factorization; see Lichtman arXiv:2109.02851, equation (5.18) for the ordinary sieve support.

import Mathlib

theorem Erdos287.sieve_two_factor_prefix_partition (xs : List ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hprefix : ∀ (l : List ℝ) (x : ℝ) (r : List ℝ), xs = l ++ x :: r →
      l.sum + x + x ≤ a + b) :
    ∃ left right : List ℝ, xs.Perm (left ++ right) ∧
      left.sum ≤ a ∧ right.sum ≤ b := by sorry
