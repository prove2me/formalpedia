-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_ae_comparison
-- name    : AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_ae_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:09:02.348893+00:00
-- url     : https://prove2.me/theorems/5f543d05-bce0-4698-83f3-94bc3d262a45
-- title:
--   Almost-everywhere polynomial comparison for two finite measures
-- statement:
--   For two finite measures, an integrable transformed test f and integrable surrogate g whose absolute error is at most δ almost everywhere under each measure, the difference of their f-integrals is at most the g-integral difference plus δ times their combined masses. This AE variant is exactly applicable to measures supported on the compact exponential-image interval after uniform polynomial approximation, without requiring any control of the approximation off the support.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_integral_uniform_error_bound
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_ae_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f g : Ω → ℝ)
    (hfμ : Integrable f μ) (hgμ : Integrable g μ)
    (hfν : Integrable f ν) (hgν : Integrable g ν)
    (δ : ℝ)
    (hδμ : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ δ)
    (hδν : ∀ᵐ ω ∂ν, |f ω - g ω| ≤ δ) :
    |(∫ ω, f ω ∂μ) - (∫ ω, f ω ∂ν)| ≤
      |(∫ ω, g ω ∂μ) - (∫ ω, g ω ∂ν)| +
        δ * (μ.real Set.univ + ν.real Set.univ) := by sorry
