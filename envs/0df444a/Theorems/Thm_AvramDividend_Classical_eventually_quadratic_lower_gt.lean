-- Prove2me | Theorems.Thm_AvramDividend_Classical_eventually_quadratic_lower_gt
-- name    : AvramDividend.Classical.eventually_quadratic_lower_gt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:24:15.430617+00:00
-- url     : https://prove2.me/theorems/83478a4c-860e-47f3-bb5f-1551c1f78215
-- title:
--   A strictly positive quadratic lower bound eventually exceeds any discount rate
-- statement:
--   For every A>0, b, D and q, the real quadratic A θ²+b θ−D exceeds q for all sufficiently large nonnegative θ. This is the deterministic final step in proving that the Gaussian component of the Avram Lévy exponent dominates negative-jump and drift terms.
-- source:
--   Elementary polynomial growth: choose B at least one and (|b|+|D|+|q|+2)/A, control the potentially negative drift, jump constant and discount by the positive quadratic term. No local Lean invocation; remote verifier authoritative.

import Mathlib

namespace AvramDividend.Classical

theorem eventually_quadratic_lower_gt
    (A b D q : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ θ : ℝ, B ≤ θ → q < A * θ ^ 2 + b * θ - D := by
  sorry

end AvramDividend.Classical
