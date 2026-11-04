-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_band_polynomial_test_error
-- name    : AvramDividend.Classical.avram_p2_b_rate_finite_band_polynomial_test_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:22:33.243134+00:00
-- url     : https://prove2.me/theorems/6463af64-b660-4869-8d01-172a1a73ff2a
-- title:
--   Quantitative finite-band reduction of continuous tests to polynomial moments
-- statement:
--   For any continuous real test on the compact exponential image interval and any positive error tolerance, select a single Weierstrass polynomial uniformly approximating the test on [0,1]. For two finite measures each almost everywhere supported there and integrable test and polynomial evaluations, the discrepancy between their original test integrals is bounded by the discrepancy between their polynomial moment integrals plus the tolerance times their total masses. This supplies the explicit finite-error bridge needed to pass moment limits through weak convergence and does not assume source rates.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_ae_comparison
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_finite_band_polynomial_test_error
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Polynomial ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ) ∧
      (Integrable (fun x : ℝ => p.eval x) μ →
       Integrable (fun x : ℝ => p.eval x) ν →
       |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
         |(∫ x, p.eval x ∂μ) - (∫ x, p.eval x ∂ν)| +
         δ * (μ.real Set.univ + ν.real Set.univ)) := by sorry
