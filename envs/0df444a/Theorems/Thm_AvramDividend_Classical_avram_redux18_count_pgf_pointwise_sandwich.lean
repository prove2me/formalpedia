-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_count_pgf_pointwise_sandwich
-- name    : AvramDividend.Classical.avram_redux18_count_pgf_pointwise_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:30:27.503412+00:00
-- url     : https://prove2.me/theorems/048020c9-850a-4ad4-bc6a-8b497ead9031
-- title:
--   Pointwise geometric generating-function bounds for integer event counts
-- statement:
--   For every integer count n and 0≤z≤1, its PGF monomial z^n lies between 1-(1-z)n and the Bernoulli indicator envelope equal to 1 at n=0 and z otherwise. Integrating and using the original counting-process mean and void probability yields a small-time PGF sandwich, supporting a direct Poisson count law through independent stationary time increments and a limit.
-- source:
--   Exact finite induction on n with nonnegative powers and the geometric Bernoulli bound. This complements the accepted Redux18 Poisson void-error quadratic lemma and provides a reusable element in the direct source-to-Poisson process characterisation.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_redux18_count_pgf_pointwise_sandwich
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    1 - (1 - z) * (n : ℝ) ≤ z ^ n ∧
      z ^ n ≤ (if n = 0 then (1 : ℝ) else z) := by sorry
