-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_poisson_void_small_time_quadratic
-- name    : AvramDividend.Classical.avram_redux18_poisson_void_small_time_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:47:21.350379+00:00
-- url     : https://prove2.me/theorems/326891d9-a264-47d1-93de-8c06711a050e
-- title:
--   Quadratic rare-event error bound from Poisson void probability
-- statement:
--   For a rate-time product between zero and one, the difference between the mean count r and the probability 1-exp(-r) of at least one Poisson-style event is nonnegative and at most r squared. This quantitative small-interval bound is the key O(h²) estimate in a binomial rare-event proof that a nonnegative integer-valued process with independent stationary increments, mean λt and void probability exp(-λt) must have Poisson count law.
-- source:
--   Uses the pinned Mathlib real exponential lower tangent inequality and second-order exponential Taylor remainder bound. Needed to derive finite negative-band actual-process full Poisson count laws from already Proved mean and void identities, without an assumed canonical PRM.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_redux18_poisson_void_small_time_quadratic
    (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    0 ≤ r + Real.exp (-r) - 1 ∧
      r + Real.exp (-r) - 1 ≤ r ^ 2 := by sorry
