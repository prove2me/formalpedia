-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:01:21.81173+00:00
-- url     : https://prove2.me/theorems/06d0ee47-d8c7-4b6c-a809-282e1d32d6f5
-- title:
--   Original finite-band raw second moment from factorial moment
-- statement:
--   The actual original intrinsic marked-jump count first and second factorial moments under physical P imply its raw second moment is the rate squared plus the rate.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
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
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2) :
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r := by sorry
