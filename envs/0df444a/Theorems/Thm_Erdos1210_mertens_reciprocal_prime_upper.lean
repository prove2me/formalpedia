-- Prove2me | Theorems.Thm_Erdos1210_mertens_reciprocal_prime_upper
-- name    : Erdos1210.mertens_reciprocal_prime_upper
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T16:34:55.888347+00:00
-- url     : https://prove2.me/theorems/0c9fc18f-bfc8-4a62-8984-30f9328300aa
-- title:
--   Mertens upper bound for prime reciprocals (Erdos 1210 analytic input)
-- statement:
--   Mertens' second theorem, upper-bound form: there exists an absolute constant C such that for every n ≥ 2, the sum of prime reciprocals below n satisfies ∑_{p<n} 1/p ≤ log(log(n)) + C. This is the analytic-number-theory input for Erdős Problem 1210 (it is not currently in Mathlib, which has only divergence of ∑ 1/p and Chebyshev θ/ψ bounds).
-- source:
--   Mertens' second theorem; analytic input for Erdős Problem #1210, https://www.erdosproblems.com/1210.

import Mathlib

namespace Erdos1210

theorem mertens_reciprocal_prime_upper :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      Finset.sum (Finset.filter Nat.Prime (Finset.range n)) (fun p => 1 / (p : ℝ)) ≤
        Real.log (Real.log (n : ℝ)) + C := by sorry

end Erdos1210
