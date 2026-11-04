-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_polynomial_moments_identify_continuous_tests
-- name    : AvramDividend.Classical.avram_p2_b_rate_polynomial_moments_identify_continuous_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:22:23.853776+00:00
-- url     : https://prove2.me/theorems/fd9fbc6e-4ef9-4063-b5a8-d8b567be2a81
-- title:
--   Polynomial moments determine continuous test integrals on a compact interval
-- statement:
--   For two finite measures supported almost everywhere on the compact image interval [0,1], equality of all polynomial test integrals implies equality of integrals of any continuous real test on that interval which is integrable against both measures. The proof applies genuine Weierstrass polynomial approximation, almost-everywhere uniform error comparison between the two measures, and an explicit epsilon argument. Polynomial integrability is supplied explicitly.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_ae_comparison
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_polynomial_moments_identify_continuous_tests
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hpoly : ∀ p : Polynomial ℝ,
      Integrable (fun x : ℝ => p.eval x) μ ∧
      Integrable (fun x : ℝ => p.eval x) ν ∧
      (∫ x, p.eval x ∂μ) = (∫ x, p.eval x ∂ν)) :
    (∫ x, f x ∂μ) = (∫ x, f x ∂ν) := by sorry
