-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:26:18.757949+00:00
-- url     : https://prove2.me/theorems/e77e3668-9133-4356-b154-04c14a4a1842
-- title:
--   Original finite-band compensated variance from factorial moment
-- statement:
--   Original P2 first and second factorial moments of the actual intrinsic marked jump count imply exact compensated diagonal variance under physical probability P.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by sorry
