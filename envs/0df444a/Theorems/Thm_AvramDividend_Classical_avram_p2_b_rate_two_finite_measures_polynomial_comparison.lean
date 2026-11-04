-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_polynomial_comparison
-- name    : AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_polynomial_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:05:53.840999+00:00
-- url     : https://prove2.me/theorems/5a26dac5-1d44-4a91-a476-33c1b2c50f29
-- title:
--   Polynomial approximation comparison bound for two finite measures
-- statement:
--   For two finite measures and an integrable target test f uniformly within δ of a polynomial or other integrable surrogate g, the discrepancy of f-integrals between those two measures is bounded by the discrepancy of g-integrals plus δ times their combined total masses. This exact quantitative comparison is a central deterministic step to deduce convergence of compact-negative transformed tests from convergence of polynomial moments and a uniform mass bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_integral_uniform_error_bound
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_polynomial_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f g : Ω → ℝ)
    (hfμ : Integrable f μ) (hgμ : Integrable g μ)
    (hfν : Integrable f ν) (hgν : Integrable g ν)
    (δ : ℝ) (hδ : ∀ ω, |f ω - g ω| ≤ δ) :
    |(∫ ω, f ω ∂μ) - (∫ ω, f ω ∂ν)| ≤
      |(∫ ω, g ω ∂μ) - (∫ ω, g ω ∂ν)| +
        δ * (μ.real Set.univ + ν.real Set.univ) := by sorry
