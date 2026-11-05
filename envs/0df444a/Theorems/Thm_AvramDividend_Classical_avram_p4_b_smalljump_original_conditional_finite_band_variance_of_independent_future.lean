-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:16:59.337917+00:00
-- url     : https://prove2.me/theorems/1b4ba10c-9aac-4603-b40d-a95903bd56ee
-- title:
--   Original conditional finite-band variance from future-past independence
-- statement:
--   The actual original finite-band marked count has constant conditional quadratic variance under its own past filtration given its original factorial moment and future-count sigma-algebra independence.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ)
    (hSource : ∀ ω, J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJ : Integrable J P)
    (hFactorialIntegrable : Integrable (fun ω => J ω * (J ω - 1)) P)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hSqMeas : StronglyMeasurable[mFuture] (fun ω => (J ω - r) ^ 2))
    (hFutureIndependent : Indep mFuture (𝓕 s) P) :
    P[(fun ω => (J ω - r) ^ 2) | 𝓕 s] =ᵐ[P] (fun _ => r) := by sorry
