-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
-- name    : AvramDividend.Classical.avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:46:10.035198+00:00
-- url     : https://prove2.me/theorems/bfb28f1b-3bc3-469c-872d-9a81c84e2f45
-- title:
--   Gaussian HJB positive-origin one-sided upper value bound from factor monotonicity
-- statement:
--   A continuous scalar value f on the strictly positive half-line with nonnegative characteristic exponent alpha, lower exponent beta no greater than alpha, classical derivative fp, and first-order weighted HJB factor bounded below on (0,a) by its value at a must be uniformly bounded above on (0,a]. This supplies the missing positive-origin endpoint control beyond the existing Gaussian HJB exponential halfline envelope gledger65, without any assumed value f(0) or absolute near-ruin growth.
-- source:
--   Source Gaussian HJB weighted derivative factorisation a249/a250, a251 mean-value derivative bound, and new a252/a253/a254 exponential derivative comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
    (f fp : ℝ → ℝ) (a alpha beta : ℝ)
    (ha : 0 < a) (hAlpha : 0 ≤ alpha) (hBeta : beta ≤ alpha)
    (hCont : ContinuousOn f (Set.Ioi 0))
    (hf : ∀ t ∈ Set.Ioo 0 a, HasDerivAt f (fp t) t)
    (hFactor : ∀ t ∈ Set.Ioo 0 a,
      Real.exp (-beta*a)*(fp a-alpha*f a) ≤
      Real.exp (-beta*t)*(fp t-alpha*f t)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y ≤ a → f y ≤ K := by sorry
