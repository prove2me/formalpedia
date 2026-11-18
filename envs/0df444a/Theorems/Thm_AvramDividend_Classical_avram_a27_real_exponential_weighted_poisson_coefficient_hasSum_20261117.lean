-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117
-- name    : AvramDividend.Classical.avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:56:50.471828+00:00
-- url     : https://prove2.me/theorems/5b4b369b-c6c9-45fc-b608-0aa6d1967042
-- title:
--   Real exponential is the exact weighted Poisson factorial power series for arbitrary real rate and argument
-- statement:
--   The sum over all k of z^k exp(-r)q^k/k! equals exp(qz-r) for every real r,q,z. This supplies exact explicit coefficients for the exponential marked-Poisson generating function in the source-free analytic part of the original Campbell/Mecke recurrence.
-- source:
--   Pinned Mathlib exponential power series NormedSpace.expSeries_div_hasSum_exp and real exponential multiplication formula.

import Mathlib
open Real MeasureTheory
open scoped BigOperators
noncomputable section

/-- The ordinary exponential has its exact real Poisson-weighted coefficient series. -/

theorem AvramDividend.Classical.avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117 (r q z : ℝ) :
    HasSum (fun k : ℕ =>
        z ^ k * (Real.exp (-r) * (q ^ k / (k.factorial : ℝ))))
      (Real.exp (q * z - r)) := by sorry
